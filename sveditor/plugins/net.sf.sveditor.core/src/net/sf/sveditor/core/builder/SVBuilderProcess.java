package net.sf.sveditor.core.builder;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent.Type;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVBuilderProcess extends Process 
	implements ILogLevel, ISVBuilderOutput {
	
	private LogHandle				fLog;
	private IProgressMonitor		fMonitor;
	private IProject				fProject;
	private int						fKind;
	private Map<String, String>		fArgs;
	private IResourceDelta			fDelta;
	private int						fExitValue = 0;
	private Object					fExitObj = new Object();
	private boolean					fIsRunning = true;
	private InputStreamFifo			fStdout = new InputStreamFifo();
	private InputStreamFifo			fStderr = new InputStreamFifo();
	
	public SVBuilderProcess(
			IProgressMonitor		monitor,
			IProject				p,
			int						kind,
			Map<String, String>		args,
			IResourceDelta			delta) {
		fMonitor = monitor;
		fProject = p;
		fKind = kind;
		fArgs = args;
		fDelta = delta;
		fLog = LogFactory.getLogHandle("SVBuilderProcess");
	}
	
	public IProject getProject() {
		return fProject;
	}
	
	public void run() {
		fIsRunning = true;
		
		
		try {
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		switch (fKind) {
		case IncrementalProjectBuilder.CLEAN_BUILD:
		case IncrementalProjectBuilder.FULL_BUILD:
			// Rebuild the target project
			note("Running clean/full re-index of project " + fProject.getName());
			pmgr.rebuildProject(fMonitor, fProject, this);
			break;
			
		case IncrementalProjectBuilder.AUTO_BUILD:
		case IncrementalProjectBuilder.INCREMENTAL_BUILD: {
			note("Running incremental re-index of project " + fProject.getName());
			
			final List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
			
			try {
				fDelta.accept(new IResourceDeltaVisitor() {
					
					public boolean visit(IResourceDelta delta) throws CoreException {
						SVDBIndexResourceChangeEvent.Type type = null;
						switch (delta.getKind()) {
							case IResourceDelta.CHANGED: 
								// We don't care about changes like markers
								if ((delta.getFlags() & IResourceDelta.CONTENT) != 0) {
									type = Type.CHANGE;
								}
								break;
							case IResourceDelta.REMOVED: 
								type = Type.REMOVE;
								break;
						}
						
						if (delta.getResource() instanceof IProject) {
							if ((delta.getFlags() & IResourceDelta.OPEN) != 0) {
								return false;
							} else if (delta.getKind() == IResourceDelta.REMOVED) {
								return false;
							}
						} else if (delta.getResource() instanceof IFile) {
							if (type != null) {
								changes.add(new SVDBIndexResourceChangeEvent(
										type, "${workspace_loc}" + delta.getResource().getFullPath()));
							}
						}
						
						return true;
					}
				});
				} catch (CoreException e) {}
		
				note("Total of " + changes.size() + " changes");
				pmgr.rebuildProject(fMonitor, fProject, changes, this);
			} break;
		}
		} finally {
			end();
		}
	}

	@Override
	public void destroy() {
		fExitValue = 1; // ?
		fMonitor.setCanceled(true);
		end();
	}
	
	@Override
	public void println(String msg) {
		fStdout.write(msg + "\n");
	}
	
	private static String timestamp() {
		SimpleDateFormat format = new SimpleDateFormat("HH:mm:ss");
		
		return format.format(new Date());
	}
	
	public void note(String msg) {
		println(timestamp() + " " + msg);
	}

	@Override
	public void errln(String msg) {
		fStderr.write(msg + "\n");
	}
	
	public void error(String msg) {
		errln(timestamp() + " Error: " + msg);
	}

	private void end() {
		fIsRunning = false;
		fStderr.end();
		fStdout.end();
		synchronized (fExitObj) {
			fExitObj.notifyAll();
		}
	}

	@Override
	public int exitValue() {
		synchronized (fExitObj) {
			if (fIsRunning || fStderr.active() || fStdout.active()) {
				// Important to signal DebugConsole that we're still running
				throw new IllegalThreadStateException();
			} else {
				return fExitValue;
			}
		}
	}

	@Override
	public InputStream getErrorStream() {
		return fStderr;
	}

	@Override
	public InputStream getInputStream() {
		return fStdout;
	}

	@Override
	public OutputStream getOutputStream() {
		// Null
		return new ByteArrayOutputStream();
	}

	@Override
	public int waitFor() throws InterruptedException {
		while (true) {
			synchronized (fExitObj) {
				if (!fIsRunning) {
					break;
				} else {
					fExitObj.wait();
				}
			}
		}
		fStdout.waitFor();
		fStderr.waitFor();
		return fExitValue;
	}

}

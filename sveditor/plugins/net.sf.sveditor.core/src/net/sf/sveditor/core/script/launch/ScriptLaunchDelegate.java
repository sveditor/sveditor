package net.sf.sveditor.core.script.launch;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.script.launch.ScriptMessage.MessageType;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;

public class ScriptLaunchDelegate implements ILaunchConfigurationDelegate {
	private List<ILogMessageScanner>			fScanners;
	private LogMessageScannerMgr				fScannerMgr;
	private LogHandle							fLog;

	public ScriptLaunchDelegate() {
		// TODO Auto-generated constructor stub
		fScanners = new ArrayList<ILogMessageScanner>();
		fLog = LogFactory.getLogHandle("ScriptLaunchDelegate");
	}

	@Override
	public void launch(
			ILaunchConfiguration 	configuration, 
			String 					mode,
			ILaunch 				launch, 
			IProgressMonitor 		monitor) throws CoreException {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		String script = configuration.getAttribute(BuildScriptLauncherConstants.SCRIPT_LIST, "");
		String wd = configuration.getAttribute(BuildScriptLauncherConstants.WORKING_DIR, System.getProperty("user.dir"));
		String args_str = configuration.getAttribute(BuildScriptLauncherConstants.ARGUMENTS, "");
		String scanners = configuration.getAttribute(BuildScriptLauncherConstants.SCANNERS, "");
		ScriptMessageScannerRegistry rgy = new ScriptMessageScannerRegistry();
		
		fScannerMgr = new LogMessageScannerMgr(wd);


		if (scanners != null && scanners.length() > 0) {
			for (String id : scanners.split(",")) {
				id = id.trim();

				if (id.equals("")) {
					continue;
				}

				ScriptMessageScannerDescriptor d = rgy.getDescriptor(id);

				if (d != null) {
					ILogMessageScanner scanner = d.getScanner();

					if (scanner != null) {
						fScannerMgr.addScanner(scanner);
					}
				}
			}
		} else {
			// Add all scanners
			for (ScriptMessageScannerDescriptor d : rgy.getDescriptors()) {
				fScannerMgr.addScanner(d.getScanner());
			}
		}
		
		monitor.beginTask("Running " + script, 1000);
	
		ScriptRunner runner = new ScriptRunner();
	
		runner.setOutLineListener(stdoutLineListener);
		runner.setErrLineListener(stderrLineListener);
		
		// First, clear existing problem markers
		root.deleteMarkers(SVScriptProblem.ID, true, IResource.DEPTH_INFINITE);
	
		File wd_f = SVFileUtils.getFile(wd);
		
		if (script.startsWith("${workspace_loc}")) {
			script = SVFileUtils.getWorkspaceResource(script).getLocation().toOSString();
		}
		List<String> argv = parse_arguments(args_str);
		
		argv.add(0, script);
	
		for (int i=0; i<argv.size(); i++) {
			String arg = argv.get(i);
			
			if (arg.startsWith("${workspace_loc}")) {
				arg = SVFileUtils.getWorkspaceResource(arg).getLocation().toOSString();
			}
			
			argv.set(i, arg);
		}
		
		fScannerMgr.addMessageListener(new ILogMessageListener() {
			
			@Override
			public void message(ScriptMessage msg) {
				String path = msg.getPath();
				IFile file[] = SVFileUtils.findWorkspaceFiles(path);

				// Skip infos for now
				if (msg.getType() != MessageType.Note) {
					if (file != null && file.length > 0) {
						for (IFile f : file) {
							try {
								String mt = msg.getMarkerType();
								
								if (mt == null) {
									mt = SVScriptProblem.ID;
								}
								
								IMarker m = f.createMarker(mt);
								
								switch (msg.getType()) {
									case Error:
										m.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
										break;
									case Warning:
										m.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
										break;
									case Note:
										m.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_INFO);
										break;
								}
								m.setAttribute(IMarker.LINE_NUMBER, msg.getLineno());
								m.setAttribute(IMarker.MESSAGE, msg.getMessage());
							} catch (CoreException e) {
								//
							}
						}
					}
				}
			}
		});		
		
		try {
			int code = runner.run(argv, null, wd_f);
			
			if (code != 0) {
				fLog.error("Command exited with non-zero code: " + code);
			}
		} catch (IOException e) {
			fLog.error(e.getMessage(), e);
			e.printStackTrace();
		}

		// Finally, refresh if needed
		IContainer f = SVFileUtils.findWorkspaceFolder(wd_f.getAbsolutePath());
		if (f != null && f.exists()) {
			f.refreshLocal(IResource.DEPTH_INFINITE, new SubProgressMonitor(monitor, 1));
		}
		
		monitor.done();
	}
	
	private ILineListener				logMessageListener = new ILineListener() {
		
		@Override
		public void line(String l) {
			synchronized (fScanners) {
				fScannerMgr.line(l);
			}
		}
	};
	
	private ILineListener				stdoutLineListener = new ILineListener() {
		
		@Override
		public void line(String l) {
			ILineListener listener = SVCorePlugin.getDefault().getStdoutLineListener();
			listener.line(l);
		
			logMessageListener.line(l);
		}
	};
	
	private ILineListener				stderrLineListener = new ILineListener() {
		
		@Override
		public void line(String l) {
			ILineListener listener = SVCorePlugin.getDefault().getStderrLineListener();
			
			listener.line(l);
			
			logMessageListener.line(l);
		}
	};

	private List<String> parse_arguments(String args) {
		List<String> ret = new ArrayList<String>();
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, new StringTextScanner(args));
	
		while (lexer.peek() != null) {
			String tok = lexer.eatToken();
		
			// Convert workspace path to filesystem path
			if (tok.startsWith("${workspace_loc}")) {
				IResource r = SVFileUtils.getWorkspaceResource(tok);
				tok = r.getLocation().toOSString();
			}
			ret.add(tok);
		}
		
		return ret;
	}

}

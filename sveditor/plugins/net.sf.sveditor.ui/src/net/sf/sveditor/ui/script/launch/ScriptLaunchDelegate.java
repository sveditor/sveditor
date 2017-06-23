package net.sf.sveditor.ui.script.launch;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.script.launch.BuildScriptLauncherConstants;
import net.sf.sveditor.core.script.launch.ILogMessageListener;
import net.sf.sveditor.core.script.launch.ILogMessageScanner;
import net.sf.sveditor.core.script.launch.LogMessageScannerMgr;
import net.sf.sveditor.core.script.launch.SVScriptProblem;
import net.sf.sveditor.core.script.launch.ScriptMessage;
import net.sf.sveditor.core.script.launch.ScriptMessage.MessageType;
import net.sf.sveditor.core.script.launch.ScriptMessageScannerDescriptor;
import net.sf.sveditor.core.script.launch.ScriptMessageScannerRegistry;
import net.sf.sveditor.core.script.launch.ScriptRunner;
import net.sf.sveditor.ui.console.SVEConsole;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.ui.console.MessageConsoleStream;

public class ScriptLaunchDelegate implements ILaunchConfigurationDelegate {
	private List<ILogMessageScanner>			fScanners;
	private LogMessageScannerMgr				fScannerMgr;
	private LogHandle							fLog;
	private PrintStream							fSaveOutput;
	private SVEConsole							fConsole;
	private MessageConsoleStream				fStdout;
	private MessageConsoleStream				fStderr;

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
		SubMonitor sm = SubMonitor.convert(monitor);
		fConsole = SVEConsole.getConsole(configuration.getName());
		
		fConsole.activate();
		fConsole.clearConsole();
		
		fStdout = fConsole.getStdout();
		fStderr = fConsole.getStderr();

	
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		String script = configuration.getAttribute(BuildScriptLauncherConstants.SCRIPT_LIST, "");
		String wd = configuration.getAttribute(BuildScriptLauncherConstants.WORKING_DIR, System.getProperty("user.dir"));
		String args_str = configuration.getAttribute(BuildScriptLauncherConstants.ARGUMENTS, "");
		
		// Expand any variables
		script = SVFileUtils.expandVars(script, null, false);
		wd = SVFileUtils.expandVars(wd, null, false);
		args_str = SVFileUtils.expandVars(args_str, null, false);

		
		String scanners = configuration.getAttribute(BuildScriptLauncherConstants.SCANNERS, "");
		String save_output_file = configuration.getAttribute("org.eclipse.debug.ui.ATTR_CAPTURE_IN_FILE", (String)null);
		ScriptMessageScannerRegistry rgy = new ScriptMessageScannerRegistry();
		
		fScannerMgr = new LogMessageScannerMgr(wd);
		
		ScriptConsolePatternMatcherFactory.addPatternMatchers(fScannerMgr, fConsole);

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
		
		sm.beginTask("Running " + script, 1000);
		
		if (save_output_file != null) {
			try {
				IStringVariableManager vman = VariablesPlugin.getDefault().getStringVariableManager();
				save_output_file = vman.performStringSubstitution(save_output_file);
			} catch (CoreException e) { 
				save_output_file = null;
			}
			
			if (save_output_file != null) {
				
			}
		}
	
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
		
		fScannerMgr.addMessageListener(msgScannerListener);
		
		try {
			int code = runner.run(argv, null, wd_f);
			
//			if (code != 0) {
//				fLog.error("Command exited with non-zero code: " + code);
//			}
		} catch (IOException e) {
			fLog.error(e.getMessage(), e);
			e.printStackTrace();
		}
		
		// Close down the listener
		fScannerMgr.close();

		// Finally, refresh if needed
		// TODO: This should probably be optional
		IContainer f = SVFileUtils.findWorkspaceFolder(wd_f.getAbsolutePath());
		if (f != null && f.exists()) {
			f.refreshLocal(IResource.DEPTH_INFINITE, sm.newChild(1));
		}
		
		sm.done();
	}
	
	private ILogMessageListener msgScannerListener = new ILogMessageListener() {
		
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

	};
	
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
			synchronized (logMessageListener) {
				fStdout.println(l);
				logMessageListener.line(l);
			}
		}
	};
	
	private ILineListener				stderrLineListener = new ILineListener() {
		@Override
		public void line(String l) {
			synchronized (logMessageListener) {
				fStderr.println(l);
				logMessageListener.line(l);
			}
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

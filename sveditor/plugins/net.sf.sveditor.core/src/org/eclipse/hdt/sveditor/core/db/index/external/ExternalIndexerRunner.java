/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.index.external;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexBuildData;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.osgi.framework.Bundle;

public class ExternalIndexerRunner {
	private static List<ExternalIndexerRunner>		fRunnerList;
	private ExternalIndexerServer					fServer;
	private Process									fProcess;
	private int										fBusyCount;
	private Listener								fStdout;
	private Listener								fStderr;
	private LogHandle								fLog;
	// TODO: timeout thread
	
	static {
		fRunnerList = new ArrayList<ExternalIndexerRunner>();
	}
	
	public static synchronized ExternalIndexerRunner allocRunner() {
		ExternalIndexerRunner runner = null;
		
		while (fRunnerList.size() > 0) {
			runner = fRunnerList.remove(0);
		
			// Mark the runner active so it's not automatically 
			// killed for a little bit
			if (runner.markActive()) {
				break;
			}
		}
		
		if (runner == null) {
			runner = new ExternalIndexerRunner();
			// TODO: startup
			runner.start();
		}
		
		return runner;
	}
	
	public static synchronized void freeRunner(ExternalIndexerRunner runner) {
		fRunnerList.add(runner);
	}
	
	public static void shutdownRunners() {
		synchronized (fRunnerList) {
			for (ExternalIndexerRunner runner : fRunnerList) {
				runner.shutdown();
			}
		}
	}
	
	private ExternalIndexerRunner() {
		fLog = LogFactory.getLogHandle("ExternalIndexRunner");

	}
	
	public void shutdown() {
		// Should mark as a dead runner
		
		// Send a shutdown request
		fServer.send_exit_msg();
		
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
		msg.write_str(ExternalIndexerMsgType.EXIT_MSG.toString());
		
		System.out.println("--> Wait process");
		try {
			fProcess.waitFor(10000, TimeUnit.MILLISECONDS);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("<-- Wait process");

		// Somehow the process didn't actually die
		if (fProcess.isAlive()) {
			fLog.error("Remote Index Process failed to terminate");
			fProcess.destroyForcibly();
		}
	
		// Ensure process is reaped
		fProcess.exitValue();
	
		System.out.println("--> Shutdown I/O threads");
		// Wait for a bit for the process to exit
		try { fStdout.join(10000); } catch (InterruptedException e) { }
		try { fStderr.join(10000); } catch (InterruptedException e) { }
		System.out.println("<-- Shutdown I/O threads");
		
		fServer.shutdown();
		
//		// Finally, wait for the server thread to exit
//		System.out.println("--> Wait server");
//		try { 
//			fServer.join(10000);
//		} catch (InterruptedException e) { }
//		System.out.println("<-- Wait server");
//		
//		if (fServer.isAlive()) {
//			System.out.println("Error: server still alive");
//		}
	}
	
	private void start() {
		try {
			fServer = new ExternalIndexerServer();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		String this_pkg = getClass().getPackage().getName();
		File java_home = new File(System.getProperty("java.home"));
		
		File jre = new File(java_home, "bin/javaw.exe");
		if (!jre.isFile()) {
			jre = new File(java_home, "bin/java");
		}
		
		List<String> cmdline = new ArrayList<String>();
		cmdline.add(jre.getAbsolutePath());
		
		String cp = buildClassPath();
		cmdline.add("-cp");
		cmdline.add(cp.toString());
		
		for (String opt : new String[] {
//				"-XX:+UseLargePages",
				"-XX:+AggressiveOpts",
				"-XX:+UseFastAccessorMethods",
//				"-Xmx4096m",
//				"-XX:+UseStringCache",
//				"-XX:+OptimizeStringConcat",
//				"-XX:SoftRefLRUPolicyMSPerMB=10000"
//				"-XX:+UseCompressedStrings"
//				"-XX:+OptimizeStringConcat"
				}) {
			cmdline.add(opt);
		}
		
	
		// Next, add the main class
		cmdline.add(this_pkg + "." + ExternalIndexerApp.class.getSimpleName());
		
		// Finally, add arguments to the main class
		cmdline.add("-port");
		cmdline.add("" + fServer.getListeningPort());
		
		try {
			fProcess = Runtime.getRuntime().exec(
					cmdline.toArray(new String[cmdline.size()])
					);
		} catch (IOException e) {
			e.printStackTrace();
		}
	
		fStdout = new Listener(fProcess.getInputStream());
		fStderr = new Listener(fProcess.getErrorStream());
			
		fStdout.start();
		fStderr.start();
			
		try {
			System.out.println("--> Connect");
			fServer.connect();
			System.out.println("<-- Connect");
		} catch (IOException e) {
			e.printStackTrace();
		}
			
		//
		markActive();
		
		// TODO: Launch timeout thread
	}

	public void build_index(
			String						argfile,
			IProgressMonitor			monitor,
			SVDBArgFileIndexBuildData	build_data) {
		fServer.do_index(argfile, monitor, build_data);
	}
	
	private boolean markActive() {
		// TODO:
		return true;
	}

	private static final class Listener extends Thread {
		private InputStream			fIn;
		public Listener(InputStream in) {
			fIn = in;
		}
		
		public void run() {
			while (true) {
				try {
					int c = fIn.read();
					if (c > 0) {
						System.out.print((char)c);
					} else {
						break;
					}
				} catch (IOException e) {
					break;
				}
			}
		}
	}
	
	private String buildClassPath() {
		StringBuilder cp = new StringBuilder();
	
		String plugin_loc = getPluginLocation(SVCorePlugin.getDefault().getBundle());
		File plugin = new File(plugin_loc);
		File plugin_cp = new File(plugin, "bin");
		
		if (!plugin_cp.isDirectory()) {
			plugin_cp = plugin;
		}
		addPath(cp, plugin_cp.getAbsolutePath());
		
		String ext_plugin = getPluginLocation(Platform.getBundle("org.eclipse.hdt.sveditor.extjar"));
		addPath(cp, ext_plugin + "/asm-4.0.jar");
		addPath(cp, ext_plugin + "/asm-commons-4.0.jar");
		
		String eclipse_home_s = System.getProperty("eclipse.home.location");
		if (eclipse_home_s.startsWith("file:/")) {
			eclipse_home_s = eclipse_home_s.substring("file:/".length());
		}
		File eclipse_home = new File(eclipse_home_s);
		
		// Add Core Runtime plugin
		addPluginPath(cp, eclipse_home, "org.eclipse.core.runtime");
		addPluginPath(cp, eclipse_home, "org.eclipse.equinox.common");
		addPluginPath(cp, eclipse_home, "org.eclipse.osgi");
		addPluginPath(cp, eclipse_home, "org.eclipse.core.resources");
		addPluginPath(cp, eclipse_home, "org.eclipse.core.variables");
		addPluginPath(cp, eclipse_home, "org.eclipse.core.jobs");
		
		return cp.toString();
	}
	
	private static String getPluginLocation(Bundle b) {
		String plugin_loc = b.getLocation();
		if (plugin_loc.startsWith("reference:")) {
			plugin_loc = plugin_loc.substring("reference:".length());
		}
		if (plugin_loc.startsWith("file:/")) {
			plugin_loc = plugin_loc.substring("file:/".length());
		}		
	
		return plugin_loc;
	}
	
	private static void addPluginPath(
			StringBuilder 		cp, 
			File 				eclipse_home, 
			String 				plugin) {
		File plugin_path = null;
		
		for (File p : new File(eclipse_home, "plugins").listFiles()) {
			String name = p.getName();
			if (name.startsWith(plugin) && 
					name.length() > plugin.length() &&
					name.charAt(plugin.length()) == '_') {
				plugin_path = p;
				break;
			}
		}
		
		System.out.println("plugin: " + plugin + " plugin_path: " + plugin_path);
		if (plugin_path != null) {
			addPath(cp, plugin_path.getAbsolutePath());
		}
	}
	
	private static void addPath(StringBuilder cp, String path) {
		char ps = System.getProperty("path.separator").charAt(0);
		if (cp.length() > 0) {
			cp.append(ps);
		}
		cp.append(path);
	}

}
	
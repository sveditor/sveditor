package net.sf.sveditor.core.db.index.external;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexBuildData;

public class ExternalIndexerRunner {
	private ExternalIndexerServer		fServer;
	
	public ExternalIndexerRunner() {
		
	}

	public void run(
			String						argfile,
			IProgressMonitor			monitor,
			SVDBArgFileIndexBuildData	build_data) {
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
		
//		for (Entry<Object, Object> pp : System.getProperties().entrySet()) {
//			System.out.println("Property: " + pp.getKey().toString() + " ; " + pp.getValue().toString());
//		}
	
		String cp = buildClassPath();
		cmdline.add("-cp");
		cmdline.add(cp.toString());
		
	
		// Next, add the main class
		cmdline.add(this_pkg + "." + ExternalIndexerApp.class.getSimpleName());
		
		// Finally, add arguments to the main class
		cmdline.add("-port");
		cmdline.add("" + fServer.getListeningPort());
		cmdline.add(argfile);
		 
		for (String arg : cmdline) {
			System.out.println("Arg: " + arg);
		}
		
		Process p = null;
		long start = System.currentTimeMillis();
		try {
			p = Runtime.getRuntime().exec(
					cmdline.toArray(new String[cmdline.size()])
					);
		} catch (IOException e) {
			e.printStackTrace();
		}
	
			Listener stdin = new Listener(p.getInputStream());
			Listener stderr = new Listener(p.getErrorStream());
			
			stdin.start();
			stderr.start();
		
			
	
		try {
			System.out.println("--> Connect");
			fServer.connect();
			System.out.println("<-- Connect");
		} catch (IOException e) {
			e.printStackTrace();
		}
		
			try { stdin.join(); } catch (InterruptedException e) { }
			try { stderr.join(); } catch (InterruptedException e) { }
			
			try {
				p.waitFor();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			
		long end = System.currentTimeMillis();
		
		System.out.println("Exec Time: " + (end-start));
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
		
		String ext_plugin = getPluginLocation(Platform.getBundle("net.sf.sveditor.extjar"));
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
	
/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDB;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVDefaultIndenter2;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.ScannerSVDBFileFactory;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;
import org.osgi.framework.Version;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCorePlugin extends Plugin implements ILogListener {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.core";
	public static final String SV_BUILTIN_LIBRARY = "net.sf.sveditor.sv_builtin";

	// The shared instance
	private static SVCorePlugin 			fPlugin;
	private SVTodoScanner					fTodoScanner;
	private SVDBProjectManager				fProjManager;
	private SVDBIndexRegistry				fIndexRegistry;
	private boolean							fDebugEn = false;
	private OutputStream					fLogStream;
	private PrintStream						fLogPS;
	public static boolean					fUseParserFactory = true; // leave scanner enabled for now
	private static Map<String, String>		fLocalEnvMap = new HashMap<String, String>();
	private SVMarkerPropagationJob			fMarkerPropagationJob;
	
	/**
	 * The constructor
	 */
	public SVCorePlugin() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		fPlugin = this;
		
		SVDB.init();
		
		fTodoScanner = new SVTodoScanner();
		
		File state_location = getStateLocation().toFile();
		
		try {
			fLogStream = new FileOutputStream(new File(state_location, "sveditor.log"));
			fLogPS = new PrintStream(fLogStream);
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		LogFactory.getDefault().addLogListener(this);
	}
	
	public void enableDebug(boolean en) {
		fDebugEn = en;
	}
	
	public boolean getDebugEn() {
		return fDebugEn;
	}
	
	public static ISVDBFileFactory createFileFactory(IDefineProvider dp) {
		if (fUseParserFactory) {
			return new ParserSVDBFileFactory(dp);
		} else {
			return new ScannerSVDBFileFactory(dp);
		}
	}
	
	public ISVIndenter createIndenter() {
		// return new SVDefaultIndenter();
		return new SVDefaultIndenter2();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		
		if (fTodoScanner != null) {
			fTodoScanner.dispose();
		}
		
		if (fProjManager != null) {
			fProjManager.dispose();
		}
		
		if (fIndexRegistry != null) {
			fIndexRegistry.save_state();
		}
		
		LogFactory.getDefault().removeLogListener(this);
		
		if (fLogStream != null) {
			fLogPS.flush();
			try {
				fLogStream.close();
			} catch (IOException e) {}
		}

		// Don't null out the plugin until we're sure we don't need it
		fPlugin = null;

		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static SVCorePlugin getDefault() {
		return fPlugin;
	}
	
	public SVDBProjectManager getProjMgr() {
		if (fProjManager == null) {
			fProjManager = new SVDBProjectManager();
		}
		return fProjManager;
	}
	
	public List<SVDBPluginLibDescriptor> getPluginLibList() {
		List<SVDBPluginLibDescriptor> ret = new ArrayList<SVDBPluginLibDescriptor>();

		IExtensionRegistry rgy = Platform.getExtensionRegistry();
		IExtensionPoint pt = rgy.getExtensionPoint(PLUGIN_ID, "SVLibraries");
		
		for (IExtension ext : pt.getExtensions()) {
			for (IConfigurationElement cel : ext.getConfigurationElements()) {
				String name       = cel.getAttribute("name");
				String path       = cel.getAttribute("path");
				String id         = cel.getAttribute("id");
				String is_dflt_s  = cel.getAttribute("default");
				String desc       = "";
				
				boolean is_default = (is_dflt_s != null && is_dflt_s.equals("true"));
				
				for (IConfigurationElement cel_i : cel.getChildren()) {
					if (cel_i.getName().equals("description")) {
						desc = cel_i.getValue();
					}
				}
				
				SVDBPluginLibDescriptor lib_desc = new SVDBPluginLibDescriptor(
						name, id, ext.getNamespaceIdentifier(), path,
						is_default, desc);
				
				ret.add(lib_desc);

			}
		}
		
		super.getStateLocation();

		return ret;
	}
	
	public SVDBIndexRegistry getSVDBIndexRegistry() {
		if (fIndexRegistry == null) {
			fIndexRegistry = new SVDBIndexRegistry();
			fIndexRegistry.init(getStateLocation().toFile());
		}
		
		return fIndexRegistry;
	}
	
	public String getDefaultSourceCollectionIncludes() {
		return "**/*.sv, **/*.svh, **/*.v, **/*.vl, **/*.vlog";
	}
	
	public String getDefaultSourceCollectionExcludes() {
		return "**/.svn/**, **/CVS/**";
	}
	
	public SVFileSet getDefaultFileSet(String base) {
		SVFileSet ret = new SVFileSet(base);
		
		for (String inc : SVDBSourceCollection.parsePatternList(getDefaultSourceCollectionIncludes())) {
			ret.addInclude(inc);
		}
		for (String exc : SVDBSourceCollection.parsePatternList(getDefaultSourceCollectionExcludes())) {
			ret.addExclude(exc);
		}
		
		return ret;
	}
	
	public void propagateMarker(IFile file, int severity, int lineno, String msg) {
		if (fMarkerPropagationJob == null) {
			fMarkerPropagationJob = new SVMarkerPropagationJob();
		}
		fMarkerPropagationJob.addMarker(file, severity, lineno, msg);
	}

	public void message(ILogHandle handle, int type, int level, String message) {
		if (type == ILogListener.Type_Error) {
			System.err.println("[" + handle.getName() + "] " + message);
			if (fLogPS != null) {
				fLogPS.println("[" + handle.getName() + "] " + message);
			}
		} else {
			if (fDebugEn) {
				System.out.println("[" + handle.getName() + "] " + message);
				if (fLogPS != null) {
					fLogPS.println("[" + handle.getName() + "] " + message);
				}
			}
		}
	}

	public String getVersion() {
		Version v = getBundle().getVersion();
		return v.getMajor() + "." + v.getMinor() + "." + v.getMicro();
	}

	
	public static StringBuilder readResourceFile(IConfigurationElement element, String attr) {
		Bundle bundle = Platform.getBundle(element.getContributor().getName());
		String filePath = element.getAttribute(attr);
		if (filePath != null) {
			URL fileURL = FileLocator.find(bundle, new Path(filePath), null);              
			if (fileURL != null) {
				try {
					StringBuilder sb = new StringBuilder();
					InputStream in = fileURL.openStream();
					byte tmp[] = new byte[1024*8];
					int sz;
					while ((sz = in.read(tmp, 0, tmp.length)) > 0) {
						for (int i=0; i<sz; i++) {
							sb.append(tmp[i]);
						}
					}
					in.close();
					return sb;
				} catch (IOException e) {}
			}       
		}
		return null;
	}
	
	public static void setenv(String key, String val) {
		if (fLocalEnvMap.containsKey(key)) {
			fLocalEnvMap.remove(key);
		}
		fLocalEnvMap.put(key, val);
	}
	
	public static String getenv(String key) {
		if (fLocalEnvMap.containsKey(key)) {
			return fLocalEnvMap.get(key);
		} else {
			return System.getenv(key);
		}
	}
}


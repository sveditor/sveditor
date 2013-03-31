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

import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileEnvVarProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFilePathVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileProjectRsrcVarProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileVariableProviderList;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDB;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.builder.SVDBIndexBuilder;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;
import net.sf.sveditor.core.db.index.cache.SVDBDirFS;
import net.sf.sveditor.core.db.index.cache.SVDBFileIndexCache;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVDefaultIndenter2;
import net.sf.sveditor.core.job_mgr.IJobMgr;
import net.sf.sveditor.core.job_mgr.JobMgr;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.templates.TemplateRegistry;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.content.IContentTypeManager;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;
import org.osgi.framework.Version;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCorePlugin extends Plugin 
	implements ILogListener, ISVDBIndexCacheFactory {
	
	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.core";
	public static final String SV_BUILTIN_LIBRARY = "net.sf.sveditor.sv_builtin";

	// The shared instance
	private static SVCorePlugin 			fPlugin;
	private SVTodoScanner					fTodoScanner;
	private SVDBProjectManager				fProjManager;
	private SVDBIndexRegistry				fIndexRegistry;
	private int								fDebugLevel = 0;
	private OutputStream					fLogStream;
	private PrintStream						fLogPS;
	private static Map<String, String>		fLocalEnvMap = new HashMap<String, String>();
	private SVMarkerPropagationJob			fMarkerPropagationJob;
	private static IJobMgr					fJobMgr;
	private int								fNumIndexCacheThreads = 0;
	private int								fMaxIndexThreads = 0;
	private TemplateRegistry				fTemplateRgy;
	private static boolean					fEnableAsyncCacheClear;
	private static boolean					fTestMode = false;
	private SVParserConfig					fParserConfig;
	private SVResourceChangeListener		fResourceChangeListener;
	private SVDBIndexBuilder				fIndexBuilder;
	
	/**
	 * The constructor
	 */
	public SVCorePlugin() {
		fParserConfig = new SVParserConfig();
		fIndexBuilder = new SVDBIndexBuilder();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		fPlugin = this;
		
		fProjManager = new SVDBProjectManager();
		fResourceChangeListener = new SVResourceChangeListener(fProjManager);
		
		if (context.getProperty("osgi.os").toLowerCase().startsWith("win")) {
			SVFileUtils.fIsWinPlatform = true;
		}
		
		SVDB.init();
		
		fTodoScanner = new SVTodoScanner();
		
		File state_location = getStateLocation().toFile();
		
		try {
			fLogStream = new FileOutputStream(new File(state_location, "sveditor.log"));
			fLogPS = new PrintStream(fLogStream);
		} catch (IOException e) {
			e.printStackTrace();
		}
	
		// Enable by default
		fEnableAsyncCacheClear = true;
		
		LogFactory.getDefault().addLogListener(this);
	}
	
	public static void setTestMode() {
		fEnableAsyncCacheClear = false;
		fTestMode = true;
	}
	
	public static boolean getTestMode() {
		return fTestMode;
	}
	
	public SVParserConfig getParserConfig() {
		return fParserConfig;
	}
	
	public boolean getEnableAsyncCacheClear() {
		return fEnableAsyncCacheClear;
	}
	
	/**
	 * Controls global enable for debug information
	 * 
	 * @param en
	 */
	public void enableDebug(boolean en) {
		fDebugLevel = (en)?ILogLevel.LEVEL_MAX:0;
		LogFactory.getDefault().setLogLevel(null, fDebugLevel);
	}
	
	public void setDebugLevel(int level) {
		fDebugLevel = level;
		LogFactory.getDefault().setLogLevel(null, fDebugLevel);
	}
	
	public void setTestDebugLevel(int level) {
		fDebugLevel = level;
		LogFactory.getDefault().setLogLevel(null, fDebugLevel);
	}
	
	public int getDebugLevel() {
		return fDebugLevel;
	}
	
	public SVDBIndexBuilder getIndexBuilder() {
		return fIndexBuilder;
	}
	
	public static ISVDBFileFactory createFileFactory(IDefineProvider dp) {
		ParserSVDBFileFactory f = new ParserSVDBFileFactory(dp);
		f.setConfig(getDefault().getParserConfig());
		
		return f;
	}
	
	public ISVIndenter createIndenter() {
		// return new SVDefaultIndenter();
		return new SVDefaultIndenter2();
	}
	
	public synchronized static IJobMgr getJobMgr() {
		if (fJobMgr == null) {
			fJobMgr = new JobMgr();
		}
		return fJobMgr;
	}
	
	public TemplateRegistry getTemplateRgy() {
		if (fTemplateRgy == null) {
			fTemplateRgy = new TemplateRegistry(true);
		}
		return fTemplateRgy;
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
		
		fResourceChangeListener.dispose();
		
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

		if (fJobMgr != null) {
			fJobMgr.dispose();
		}
		
		fIndexBuilder.dispose();
		
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
	
	public static void testInit() {
		fPlugin = new SVCorePlugin();
		LogFactory.getDefault().addLogListener(fPlugin);
	}
	
	public SVDBProjectManager getProjMgr() {
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
	
	public void setSVDBIndexRegistry(SVDBIndexRegistry rgy) {
		fIndexRegistry = rgy;
	}
	
	public SVDBIndexRegistry getSVDBIndexRegistry() {
		if (fIndexRegistry == null) {
			fIndexRegistry = new SVDBIndexRegistry();
			fIndexRegistry.init(this);
		}
		
		return fIndexRegistry;
	}
	
	public ISVDBIndexCache createIndexCache(String project_name, String base_location) {
		File file = getStateLocation().toFile();
		File cache = new File(file, "cache");
		File cache_dir = new File(cache, project_name + "_" + SVFileUtils.computeMD5(base_location));

		if (!cache_dir.exists()) {
			if (!cache_dir.mkdirs()) {
				System.out.println("Failed to create cache directory");
			}
		}
		
		SVDBDirFS fs = new SVDBDirFS(cache_dir);
		fs.setEnableAsyncClear(fEnableAsyncCacheClear);
		ISVDBIndexCache ret = new SVDBFileIndexCache(fs);

		return ret;
	}
	
	public void compactCache(List<ISVDBIndexCache> cache_list) {
		File file = getStateLocation().toFile();
		File cache = new File(file, "cache");
		if (cache.isDirectory()) {
			List<File> file_list = new ArrayList<File>();
			for (File f : cache.listFiles()) {
				if (!f.getName().equals(".") && !f.getName().equals("..")) {
					file_list.add(f);
				}
			}
			for (ISVDBIndexCache index_c : cache_list) {
				index_c.removeStoragePath(file_list);
			}
			
			for (File f : file_list) {
				System.out.println("Compacting cache: " + f.getAbsolutePath());
				SVFileUtils.delete(f);
			}
		}
	}
	
	public List<String> getDefaultSVExts() {
		IContentTypeManager mgr = Platform.getContentTypeManager();
		IContentType type = mgr.getContentType(PLUGIN_ID + ".systemverilog");
		String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

		List<String> ret = new ArrayList<String>();
		for (String e : exts) {
			ret.add(e);
		}
		
		return ret;
	}

	public String getDefaultSourceCollectionIncludes() {
		IContentTypeManager mgr = Platform.getContentTypeManager();
		IContentType type = mgr.getContentType(PLUGIN_ID + ".systemverilog");
		String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);
		StringBuilder ret = new StringBuilder();

		for (int i=0; i<exts.length; i++) {
			ret.append("**/*.");
			ret.append(exts[i]);
			if (i+1 < exts.length) {
				ret.append(", ");
			}
		}
		return ret.toString();
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
	
	public void propagateMarker(IResource file, int severity, int lineno, String msg) {
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
			if (fDebugLevel >= level) {
				System.out.println("[" + handle.getName() + "] " + message);
				if (fLogPS != null) {
					fLogPS.println("[" + handle.getName() + "] " + message);
				}
			}
		}
	}

	public static String getVersion() {
		if (fPlugin != null && fPlugin.getBundle() != null) {
			Version v = fPlugin.getBundle().getVersion();
			return v.getMajor() + "." + v.getMinor() + "." + v.getMicro();
		} else {
			return "1.2.3"; // testing
		}
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
	
	public static ISVArgFileVariableProvider getVariableProvider(IProject project) {
		SVArgFileVariableProviderList ret = new SVArgFileVariableProviderList();
		
		if (project != null) {
			ret.addProvider(new SVArgFileProjectRsrcVarProvider(project));
		}
		
		try {
			IWorkspace ws = ResourcesPlugin.getWorkspace();
			ret.addProvider(new SVArgFilePathVariableProvider(ws.getPathVariableManager()));
		} catch (IllegalStateException e) {}
		
		ret.addProvider(new SVArgFileEnvVarProvider());
		
		return ret;
	}
	
	public static int getNumIndexCacheThreads() {
		SVCorePlugin plugin = getDefault();
		if (plugin != null) {
			return plugin.fNumIndexCacheThreads;
		} else {
			return 0;
		}
	}
	
	public static int getMaxIndexThreads() {
		SVCorePlugin plugin = getDefault();
		if (plugin != null) {
			return plugin.fMaxIndexThreads;
		} else {
			return 0;
		}
	}
	
	public static String[] getPersistencePkgs() {
		return new String[] {
			"net.sf.sveditor.core.db.", 
			"net.sf.sveditor.core.db.stmt.",
			"net.sf.sveditor.core.db.expr.",
			"net.sf.sveditor.core.db.argfile."
		};
	}
	
	public File createWSTmpDir() {
		File state_loc = getStateLocation().toFile();
		File state_tmpdir = new File(state_loc, "tmpdir");
		
		if (!state_tmpdir.isDirectory()) {
			state_tmpdir.mkdirs();
		}
		
		File tmp  = null;
		
		try {
			tmp = File.createTempFile("XXXX", "XXXX", state_tmpdir);
		} catch (IOException e) {
			e.printStackTrace();
		}
	
		tmp.delete();
		tmp.mkdirs();
		
		return tmp;
	}
	
}


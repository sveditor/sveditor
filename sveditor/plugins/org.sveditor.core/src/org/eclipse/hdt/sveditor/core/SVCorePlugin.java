/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core;

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

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.content.IContentTypeManager;
import org.eclipse.hdt.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileEnvVarProvider;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFilePathVariableProvider;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileProjectRsrcVarProvider;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileVariableProviderList;
import org.eclipse.hdt.sveditor.core.builder.CoreBuildProcessListener;
import org.eclipse.hdt.sveditor.core.builder.CoreBuilderOutputListener;
import org.eclipse.hdt.sveditor.core.builder.ISVBuildProcessListener;
import org.eclipse.hdt.sveditor.core.builder.ISVBuilderOutputListener;
import org.eclipse.hdt.sveditor.core.db.ISVDBFileFactory;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexBuilder;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.index.cache.delegating.SVDBSegmentedIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.index.cache.file.SVDBFileSystem;
import org.eclipse.hdt.sveditor.core.db.index.plugin.SVDBPluginLibDescriptor;
import org.eclipse.hdt.sveditor.core.db.index.plugin.SVDBPluginLibIndexFactory;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVDBSourceCollection;
import org.eclipse.hdt.sveditor.core.fileset.SVFileSet;
import org.eclipse.hdt.sveditor.core.indent.ISVIndenter;
import org.eclipse.hdt.sveditor.core.indent.SVDefaultIndenter2;
import org.eclipse.hdt.sveditor.core.job_mgr.IJobMgr;
import org.eclipse.hdt.sveditor.core.job_mgr.JobMgr;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.ILogListener;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.parser.SVParser;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;
import org.eclipse.hdt.sveditor.core.scanner.IPreProcMacroProvider;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;
import org.osgi.framework.Version;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCorePlugin extends Plugin implements ILogListener {
	
	// The plug-in ID
	public static final String PLUGIN_ID = "org.eclipse.hdt.sveditor.core";
	public static final String SV_BUILTIN_LIBRARY = "org.eclipse.hdt.sveditor.sv_builtin";
	public static final String SV_PROBLEM = PLUGIN_ID + ".svProblem";
	public static final String SV_TASK = PLUGIN_ID + ".task";

	// The shared instance
	private static SVCorePlugin 			fPlugin;
	private SVTodoScanner					fTodoScanner;
	private SVDBProjectManager				fProjManager;
	private SVDBIndexRegistry				fIndexRegistry;
	private int								fDebugLevel = 0;
	private boolean  						fFileExtensionLanguageLevelOverride  = false ;
	private OutputStream					fLogStream;
	private PrintStream						fLogPS;
	private static Map<String, String>		fLocalEnvMap = new HashMap<String, String>();
	private SVMarkerPropagationJob			fMarkerPropagationJob;
	private static IJobMgr					fJobMgr;
	private static boolean					fTestMode = false;
	private SVParserConfig					fParserConfig;
	private SVResourceChangeListener		fResourceChangeListener;
	private SVDBIndexBuilder				fIndexBuilder;
	private ISVDBIndexCacheMgr				fCacheMgr;
	private static boolean					fTestModeBuilderDisabled = false;
	// SVEditor currently supports two cache models:
	// - A unified cache that handles all projects and indexes with a single database
	// - A delegating cache that uses independent databases to handle each index
	private static final boolean			fUseDelegatingIndexCache = false;
	
	// Listeners
	private List<ILineListener>				fStdoutLineListeners = new ArrayList<ILineListener>();
	private List<ILineListener>				fStderrLineListeners = new ArrayList<ILineListener>();
	
	// Obsolete Fields
	private int								fNumIndexCacheThreads = 0;
	private int								fMaxIndexThreads = 0;
	private static boolean					fEnableAsyncCacheClear;
	private static List<String>				fPersistenceClassPkgList;
	private ISVBuilderOutputListener		fBuilderOutputListener = new CoreBuilderOutputListener();
	private ISVBuildProcessListener			fBuildProcessListener = new CoreBuildProcessListener();
	private ISVDBIndex						fBuiltinLib;
	
	static {
		fPersistenceClassPkgList = new ArrayList<String>();
		fPersistenceClassPkgList.add("org.eclipse.hdt.sveditor.core.db");
		fPersistenceClassPkgList.add("org.eclipse.hdt.sveditor.core.db.expr");
		fPersistenceClassPkgList.add("org.eclipse.hdt.sveditor.core.db.stmt");
		fPersistenceClassPkgList.add("org.eclipse.hdt.sveditor.core.db.argfile");
		fPersistenceClassPkgList.add("org.eclipse.hdt.sveditor.core.db.vhdl");
	}
	
	/**
	 * The constructor
	 */
	public SVCorePlugin() {
		fParserConfig = new SVParserConfig();
		fIndexBuilder = new SVDBIndexBuilder();
		fIndexRegistry = new SVDBIndexRegistry();
	}
	
	public static ISVDBIndexCacheMgr createCacheMgr(File cache) {
		ISVDBIndexCacheMgr ret = null;
		
		if (fUseDelegatingIndexCache) {
			SVDBSegmentedIndexCacheMgr cache_mgr = new SVDBSegmentedIndexCacheMgr();
			cache_mgr.init(cache);
			
			ret = cache_mgr;
		} else {
			SVDBFileSystem cache_fs = new SVDBFileSystem(cache, getVersion());
			try {
				cache_fs.init();
			} catch (IOException e) {
				return null;
			}
			ret = new SVDBFileIndexCacheMgr();
			((SVDBFileIndexCacheMgr)ret).init(cache_fs);
		}
		return ret;
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
		
		fTodoScanner = new SVTodoScanner();
		
		File state_location = getStateLocation().toFile();
		
		try {
			fLogStream = new FileOutputStream(new File(state_location, "sveditor.log"));
			fLogPS = new PrintStream(fLogStream);
		} catch (IOException e) {
			e.printStackTrace();
		}

		// Initialize the cache manager and filesystem
		File cache = new File(state_location, "cache2");

		if (!cache.isDirectory()) {
			cache.mkdirs();
		}
		
		fCacheMgr = createCacheMgr(cache);

		// Connect the cache manager
		fIndexRegistry.init(fCacheMgr);
	
		// Enable by default
		fEnableAsyncCacheClear = true;
		
		LogFactory.getDefault().addLogListener(this);
		
		fProjManager.init();
	}
	
	public void addStdoutLineListener(ILineListener l) {
		fStdoutLineListeners.add(l);
	}
	
	public void removeStdoutLineListener(ILineListener l) {
		fStdoutLineListeners.remove(l);
	}
	
	public void addStderrLineListener(ILineListener l) {
		fStderrLineListeners.add(l);
	}
	
	public void removeStderrLineListener(ILineListener l) {
		fStderrLineListeners.remove(l);
	}
	
	public ISVDBIndex getBuiltinLib() {
		if (fBuiltinLib == null) {
			SVDBPluginLibDescriptor desc = null;
			for (SVDBPluginLibDescriptor d : getPluginLibList()) {
				if (d.getId().equals("org.eclipse.hdt.sveditor.sv_builtin")) {
					desc = d;
					break;
				}
			}
			fBuiltinLib = fIndexRegistry.findCreateIndex(
					new NullProgressMonitor(),
					"__SVE_BUILTIN", 
					desc.getId(), 
					SVDBPluginLibIndexFactory.TYPE, 
					null);
			fBuiltinLib.execIndexChangePlan(new NullProgressMonitor(), 
					new SVDBIndexChangePlanRebuild(fBuiltinLib));
		}
		
		return fBuiltinLib;
	}
	
	private ILineListener			fStderrLineListener = new ILineListener() {
		@Override
		public void line(String msg) {
			for (ILineListener l : fStderrLineListeners) {
				l.line(msg);
			}
		}
	};

	private ILineListener			fStdoutLineListener = new ILineListener() {
		@Override
		public void line(String msg) {
			for (ILineListener l : fStdoutLineListeners) {
				l.line(msg);
			}
		}
	};
	
	public ILineListener getStdoutLineListener() {
		return fStdoutLineListener;
	}
	
	public ILineListener getStderrLineListener() {
		return fStderrLineListener;
	}
	
	public static List<String> getPersistenceClassPkgList() {
		List<String> ret = new ArrayList<String>();
		ret.addAll(fPersistenceClassPkgList);
		
		return ret;
	}
	
	public static void addPersistenceClassPkg(String pkg) {
		if (!fPersistenceClassPkgList.contains(pkg)) {
			fPersistenceClassPkgList.add(pkg);
		}
	}
	
	public SVResourceChangeListener getResourceChangeListener() {
		return fResourceChangeListener;
	}
	
	public static void setTestMode() {
		fEnableAsyncCacheClear = false;
		fTestMode = true;
	}
	
	public static boolean getTestMode() {
		return fTestMode;
	}
	
	public static void setTestModeBuilderDisabled() {
		fTestModeBuilderDisabled = true;
	}
	
	public static boolean isTestModeBuilderDisabled() {
		return fTestModeBuilderDisabled;
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
	
	public void setFileExtLanguageLevelOverride(boolean en) {
		fFileExtensionLanguageLevelOverride = en ;
	}
	
	public boolean getFileExtLanguageLevelOverride() {
		return fFileExtensionLanguageLevelOverride ;
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
	
	public static ISVDBFileFactory createFileFactory() {
		return createFileFactory(null);
	}
	
	public static ISVDBFileFactory createFileFactory(IPreProcMacroProvider mp) {
		SVParser p = new SVParser();
		p.setMacroProvider(mp);
		
		if (getDefault() != null) {
			p.setConfig(getDefault().getParserConfig());
		}
		
		return p;
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
			fIndexRegistry.close();
		}
		
		fResourceChangeListener.dispose();

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
		
		// Shut down the builder
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
	
	public void setBuilderOutputListener(ISVBuilderOutputListener l) {
		fBuilderOutputListener = l;
	}
	
	public ISVBuilderOutputListener getBuilderOutputListener() {
		return fBuilderOutputListener;
	}
	
	public void setBuildProcessListener(ISVBuildProcessListener l) {
		fBuildProcessListener = l;
	}
	
	public ISVBuildProcessListener getBuildProcessListener() {
		return fBuildProcessListener;
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
		return fIndexRegistry;
	}
	
	public ISVDBIndexCache findIndexCache(String project_name,
			String base_location) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Cache factory method
	 */
	public void dispose() {
		// TODO Auto-generated method stub
		
	}

	/**
	 * Cache manager method
	 */
	public void sync() {
		// TODO Auto-generated method stub
		
	}

	public List<String> getDefaultSVExts() {
		IContentTypeManager mgr = Platform.getContentTypeManager();
		List<String> ret = new ArrayList<String>();
		
		for (String type_s : new String[] {
				PLUGIN_ID + ".systemverilog",
				PLUGIN_ID + ".verilog",
				PLUGIN_ID + ".verilogams"}) {
			IContentType type = mgr.getContentType(type_s);
			String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

			for (String e : exts) {
				ret.add(e);
			}
		}
		
		return ret;
	}
	
	public Map<String, IContentType> getContentTypes() {
		Map<String, IContentType> ret = new HashMap<String, IContentType>();
		IContentTypeManager mgr = Platform.getContentTypeManager();
		
		for (String type_s : new String[] {
				PLUGIN_ID + ".systemverilog",
				PLUGIN_ID + ".verilog",
				PLUGIN_ID + ".verilogams"}) {
			IContentType type = mgr.getContentType(type_s);
			String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);
			
			for (String ext : exts) {
				ret.put(ext, type);
			}
		}
		
		return ret;
	}
	
	public List<String> getDefaultArgFileExts() {
		IContentTypeManager mgr = Platform.getContentTypeManager();
		IContentType type = mgr.getContentType(PLUGIN_ID + ".argfile");
		String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

		List<String> ret = new ArrayList<String>();
		for (String e : exts) {
			ret.add(e);
		}
		
		return ret;
	}

	public String getDefaultSourceCollectionIncludes() {
		IContentTypeManager mgr = Platform.getContentTypeManager();
		StringBuilder ret = new StringBuilder();
			
		for (String type_s : new String[] {".systemverilog", ".verilog", ".verilogams"}) {
			IContentType type = mgr.getContentType(PLUGIN_ID + type_s);
			if (type == null) {
				System.out.println("Failed to get type: " + PLUGIN_ID + type_s);
			}
			String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

			for (int i=0; i<exts.length; i++) {
				ret.append("**/*.");
				ret.append(exts[i]);
				ret.append(", ");
			}
		}
		
		ret.setLength(ret.length()-2);
		
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
		String handle_tag = (handle != null)?("[" + handle.getName() + "] "):"";
		if (type == ILogListener.Type_Error) {
			System.err.println(handle_tag + message);
			if (fLogPS != null) {
				fLogPS.println(handle_tag + message);
			}
		} else if (type == ILogListener.Type_Info) {
			if (fLogPS != null) {
				fLogPS.println(handle_tag + message);
			} else {
				System.out.println(handle_tag + message);
			}
		} else {
			if (fDebugLevel >= level) {
				System.out.println(handle_tag + message);
				if (fLogPS != null) {
					fLogPS.println(handle_tag + message);
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
	
	public static void clearenv() {
		fLocalEnvMap.clear();
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
			"org.eclipse.hdt.sveditor.core.db.", 
			"org.eclipse.hdt.sveditor.core.db.stmt.",
			"org.eclipse.hdt.sveditor.core.db.expr.",
			"org.eclipse.hdt.sveditor.core.db.argfile."
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


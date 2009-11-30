package net.sf.sveditor.core;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogListener;
import net.sf.sveditor.core.log.LogFactory;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCorePlugin extends Plugin implements ILogListener {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.core";

	// The shared instance
	private static SVCorePlugin 			fPlugin;
	private SVTodoScanner					fTodoScanner;
	private SVDBProjectManager				fProjManager;
	private SVDBIndexRegistry				fIndexRegistry;
	private boolean							fDebugEn = true;
	
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
		fTodoScanner = new SVTodoScanner();
		
		LogFactory.getDefault().addLogListener(this);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		fPlugin = null;
		
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

	public void message(ILogHandle handle, int type, int level, String message) {
		if (type == ILogListener.Type_Error) {
			System.err.println("[" + handle.getName() + "] " + message);
		} else {
			if (fDebugEn) {
				System.out.println("[" + handle.getName() + "] " + message);
			}
		}
	}

}



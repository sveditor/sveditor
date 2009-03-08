package net.sf.sveditor.core;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCorePlugin extends Plugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.core";

	// The shared instance
	private static SVCorePlugin 			fPlugin;
	private SVDBWorkspaceFileManager		fSVDBMgr;
	private SVTodoScanner					fTodoScanner;
	private SVDBProjectManager				fProjManager;
	private SVDBIndexList					fBuiltinList;		
	
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
		
//		loadBuiltInLibraries();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		
		fPlugin = null;
		if (fSVDBMgr != null) {
			fSVDBMgr.dispose();
			fSVDBMgr = null;
		}
		
		if (fTodoScanner != null) {
			fTodoScanner.dispose();
		}
		
		if (fProjManager != null) {
			fProjManager.dispose();
		}
		
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
	
	public SVDBWorkspaceFileManager getSVDBMgr() {
		if (fSVDBMgr == null) {
			fSVDBMgr = new SVDBWorkspaceFileManager();
		}
		return fSVDBMgr;
	}
	
	private void loadBuiltInLibraries() {
		fBuiltinList = new SVDBIndexList(new File("BUILTIN"));
		
		IExtensionRegistry rgy = Platform.getExtensionRegistry();
		
		IExtensionPoint pt = rgy.getExtensionPoint(PLUGIN_ID, "SVLibraries");
		
		for (IExtension ext : pt.getExtensions()) {
			for (IConfigurationElement cel : ext.getConfigurationElements()) {
				String name = cel.getAttribute("name");
				String path = cel.getAttribute("path");

				System.out.println("name=" + name + " @ " + path);
				SVDBPluginLibIndex index = new SVDBPluginLibIndex(name,
						Platform.getBundle(ext.getNamespaceIdentifier()), path);
				fBuiltinList.addIndex(index);
			}
		}
	}
	
	public ISVDBIndex getBuiltinIndex() {
		if (fBuiltinList == null) {
			loadBuiltInLibraries();
		}
		return fBuiltinList;
	}
}

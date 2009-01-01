package net.sf.sveditor.core;

import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCorePlugin extends Plugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.core";

	// The shared instance
	private static SVCorePlugin plugin;
	private SVDBWorkspaceFileManager			fSVDBMgr;
	private SVTodoScanner			fTodoScanner;
	private SVDBProjectManager		fProjManager;
	
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
		plugin = this;
		
		fTodoScanner = new SVTodoScanner();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
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
		return plugin;
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

}

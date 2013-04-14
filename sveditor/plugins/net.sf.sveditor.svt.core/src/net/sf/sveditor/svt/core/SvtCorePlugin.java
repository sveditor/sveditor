package net.sf.sveditor.svt.core;

import net.sf.sveditor.core.templates.TemplateRegistry;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SvtCorePlugin extends Plugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.svt.core"; //$NON-NLS-1$

	// The shared instance
	private static SvtCorePlugin 			plugin;
	
	private TemplateRegistry				fTemplateRgy;
	
	/**
	 * The constructor
	 */
	public SvtCorePlugin() {
	}
	
	public TemplateRegistry getTemplateRgy() {
		if (fTemplateRgy == null) {
			fTemplateRgy = new TemplateRegistry(true);
		}
		return fTemplateRgy;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static SvtCorePlugin getDefault() {
		return plugin;
	}

}

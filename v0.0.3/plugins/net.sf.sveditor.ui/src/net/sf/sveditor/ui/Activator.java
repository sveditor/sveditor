package net.sf.sveditor.ui;

import java.util.MissingResourceException;
import java.util.ResourceBundle;

import org.eclipse.core.internal.resources.ResourceException;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.ui";

	// The shared instance
	private static Activator plugin;
	private ResourceBundle			fResources;
	
	/**
	 * The constructor
	 */
	public Activator() {
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
	
	public ResourceBundle getResources() {
		if (fResources == null) {
			try {
				fResources = ResourceBundle.getBundle(
						PLUGIN_ID + ".SVUIResources");
			} catch (MissingResourceException e) {
				e.printStackTrace();
			}
		}
		return fResources;
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return plugin;
	}

}

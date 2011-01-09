package net.sf.sveditor.doc.user;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

public class Activator extends Plugin {
	
	private static Activator				fPlugin;

	@Override
	public void start(BundleContext context) throws Exception {

		super.start(context);
		fPlugin = this;
	}

	@Override
	public void stop(BundleContext context) throws Exception {

		fPlugin = null;
		super.stop(context);
	}
	
	
	public static Activator getDefault() {
		return fPlugin;
	}
	

}

package net.sf.sveditor.svt.app.core;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

public class SVTMainApp implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		System.out.println("AppMain");
		
		return 0;
	}

	public void stop() {
		// TODO Auto-generated method stub

	}

}

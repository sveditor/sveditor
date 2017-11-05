package net.sf.sveditor.ui.console;

import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.ui.console.IConsoleColorProvider;
import org.eclipse.jface.resource.ImageDescriptor;

public class SVProcessConsole extends SVConsole {
    private IProcess					fProcess;
	
	public SVProcessConsole(
			SVConsoleManager	mgr,
			IProcess			process,
			ImageDescriptor		img) {
		super(mgr, 
				process.getLabel(), 
				process.getAttribute(IProcess.ATTR_PROCESS_TYPE), 
				img);

		fProcess    = process;
		fStreamsProxy = fProcess.getStreamsProxy();
		fColorProvider = fConsoleMgr.getColorProvider(
				process.getAttribute(IProcess.ATTR_PROCESS_TYPE));
		fColorProvider.connect(process, this);
	}

	@Override
	public IProcess getProcess() {
		return fProcess;
	}

	
}

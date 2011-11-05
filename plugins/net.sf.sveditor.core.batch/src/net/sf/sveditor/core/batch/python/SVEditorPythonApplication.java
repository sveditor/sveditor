package net.sf.sveditor.core.batch.python;

import org.eclipse.core.runtime.Status;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.python.util.PythonInterpreter;

public class SVEditorPythonApplication implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		String args[] = (String [])context.getArguments().get(IApplicationContext.APPLICATION_ARGS);
		
		if (args.length != 1) {
			throw new Exception("wrong arguments");
		}
		
		PythonInterpreter interp = new PythonInterpreter();
		interp.execfile(args[0]);
		
		return Status.OK_STATUS;
	}

	public void stop() {
		// TODO Auto-generated method stub

	}

}

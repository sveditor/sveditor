package net.sf.sveditor.core.tests;

import java.io.InputStream;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBItem;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

public class testSVScannerLineNumbers implements IApplication {

	@Override
	public Object start(IApplicationContext context) throws Exception {
		// InputStream in = Activator.openFile("data/ovm_tlm/ovm_ports.svh");
		InputStream in = Activator.openFile("data/tlm_imps.svh");
		
		SVDBFile f =  SVDBFileFactory.createFile(in, "tlm_imps.svh");
		
		for (SVDBItem it : f.getItems()) {
			System.out.println("item \"" + it.getName() + "\" @ line " + it.getLocation().getLine());
		}
		
		return 0;
	}

	@Override
	public void stop() {}
}

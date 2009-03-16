package net.sf.sveditor.core.db;

import java.io.OutputStream;
import java.util.List;

public class SVDBDump {
	private List<SVDBScopeItem>				fItems;
	private OutputStream					fOut;
	
	public void dump(OutputStream out) {
		fOut = out;
		
		for (SVDBScopeItem scope : fItems) {
			dumpScope(scope);
		}
		
	}
	
	private void dumpScope(SVDBScopeItem scope) {
		
		for (SVDBItem item : scope.getItems()) {
			if (item instanceof SVDBScopeItem) {
				dumpScope((SVDBScopeItem)item);
			}
		}
	}
	
	private void dumpItem(SVDBItem item) {
		
	}

}

package net.sf.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;

public class SVDBRefCollectorVisitor implements ISVDBRefVisitor {
	
	private List<SVDBRefItem>				fItemList;
	
	public SVDBRefCollectorVisitor() {
		fItemList = new ArrayList<SVDBRefItem>(); 
	}
	
	public List<SVDBRefItem> getItemList() {
		return fItemList;
	}

	@Override
	public void visitRef(ISVDBRefSearchSpec ref_spec, SVDBRefItem item) {
		fItemList.add(item);
	}

	
}

package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBImportStmt extends SVDBStmt implements ISVDBChildParent {
	
	private List<SVDBImportItem>			fImportList;
	
	public SVDBImportStmt() {
		super(SVDBItemType.ImportStmt);
		fImportList = new ArrayList<SVDBImportItem>();
	}
	
	@Override
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fImportList.add((SVDBImportItem)item);
	}
	
	@Override
	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			@Override
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fImportList.iterator();
			}
		};
	}
}

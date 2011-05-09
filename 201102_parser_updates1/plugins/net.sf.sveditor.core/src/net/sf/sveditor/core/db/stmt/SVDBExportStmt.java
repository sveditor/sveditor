package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBExportStmt extends SVDBStmt implements ISVDBChildParent {
	private List<SVDBExportItem>			fExportList;
	
	public SVDBExportStmt() {
		super(SVDBItemType.ExportStmt);
		fExportList = new ArrayList<SVDBExportItem>();
	}
	
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fExportList.add((SVDBExportItem)item);
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return (Iterator)fExportList.iterator();
			}
		};
	}

}

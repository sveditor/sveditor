package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBScopeItem extends SVDBItem {
	protected List<SVDBItem>			fItems;
	protected SVDBLocation				fEndLocation;
	
	public SVDBScopeItem(String name, SVDBItemType type) {
		super(name, type);
		
		fItems = new ArrayList<SVDBItem>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBScopeItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		if (getType() == SVDBItemType.File) {
			file   = (SVDBFile)this;
		}
		fEndLocation = new SVDBLocation(file, reader.readInt(), 0);
		fItems = (List<SVDBItem>)reader.readItemList(file, this);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeInt((fEndLocation!=null)?fEndLocation.getLine():0);
		writer.writeItemList(fItems);
	}
	
	
	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}
	
	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}
	
	public void addItem(SVDBItem item) {
		item.setParent(this);
		fItems.add(item);
	}
	
	public List<SVDBItem> getItems() {
		return fItems;
	}

	public SVDBItem duplicate() {
		SVDBScopeItem ret = new SVDBScopeItem(getName(), getType());

		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
		
		SVDBScopeItem si = (SVDBScopeItem)other;
		
		fItems.clear();
		for (SVDBItem it : si.getItems()) {
			fItems.add(it.duplicate());
		}
		fEndLocation = new SVDBLocation(
				((SVDBScopeItem)other).fEndLocation);
	}
	
}

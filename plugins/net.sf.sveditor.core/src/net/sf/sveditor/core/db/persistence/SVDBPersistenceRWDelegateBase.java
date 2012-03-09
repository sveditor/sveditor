package net.sf.sveditor.core.db.persistence;

import java.io.DataInput;
import java.io.DataOutput;
import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBItemType;

public abstract class SVDBPersistenceRWDelegateBase extends SVDBPersistenceRWBase 
		implements ISVDBPersistenceRWDelegate {
	protected Set<SVDBItemType>						fSupportedItems;
	protected ISVDBPersistenceRWDelegateParent		fParent; 
	
	public SVDBPersistenceRWDelegateBase() {
		fSupportedItems = new HashSet<SVDBItemType>();
	}

	public void init(
			ISVDBPersistenceRWDelegateParent	parent, 
			DataInput 							in,
			DataOutput 							out) {
		fParent = parent;
		fIn = in;
		fOut = out;
	}

	public void init(Set<SVDBItemType> supported_items) {
		fSupportedItems.addAll(supported_items);
	}

	public Set<Class> getSupportedObjects() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<Class> getSupportedEnumTypes() {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<SVDBItemType> getSupportedItemTypes() {
		return fSupportedItems;
	}
	
}

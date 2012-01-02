package net.sf.sveditor.core.db.persistence;

public class SVDBPersistenceRW extends SVDBDelegatingPersistenceRW {
	
	public SVDBPersistenceRW() {
	
		// TODO: register other persistence delegates
		addDelegate(new SVDBBaseItemsPersistenceDelegate());
	}

}

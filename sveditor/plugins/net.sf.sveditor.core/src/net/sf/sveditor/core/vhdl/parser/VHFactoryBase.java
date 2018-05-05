package net.sf.sveditor.core.vhdl.parser;

import net.sf.sveditor.core.db.ISVDBChildItem;

public class VHFactoryBase extends vhdlBaseVisitor<ISVDBChildItem> implements IVHFactory {
	protected VHFactories			fFactories;
	
	public VHFactoryBase(VHFactories f) {
		fFactories = f;
	}

	@Override
	public void init(VHFactories f) {
		fFactories = f;
	}

}

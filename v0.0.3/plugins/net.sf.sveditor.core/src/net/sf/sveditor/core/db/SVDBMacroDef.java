package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBMacroDef extends SVDBItem {
	
	private List<String>			fParams;
	private String					fDef;
	
	public SVDBMacroDef(
			String 				name, 
			List<String>		params,
			String				def) {
		super(name, SVDBItemType.Macro);
		fParams = new ArrayList<String>();
		fParams.addAll(params);
		fDef = def;
	}
	
	public String getDef() {
		return fDef;
	}

	@Override
	public SVDBItem duplicate() {
		SVDBMacroDef ret = new SVDBMacroDef(
				getName(), fParams, fDef);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		super.init(other);
		
		SVDBMacroDef m = (SVDBMacroDef)other;
		fParams.clear();
		fParams.addAll(m.fParams);
		fDef = m.fDef;
	}
	
}

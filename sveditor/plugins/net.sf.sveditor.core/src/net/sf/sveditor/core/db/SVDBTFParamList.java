package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;

public class SVDBTFParamList extends SVDBItemBase implements ISVDBChildParent {
	private ISVDBChildItem				fParent;
	private List<SVDBParamPortDecl>		fParams;

	public SVDBTFParamList() {
		super(SVDBItemType.TFParamList);
		fParams = new ArrayList<>();
	}
	
	public SVDBTFParamList(List<SVDBParamPortDecl> params) {
		super(SVDBItemType.TFParamList);
		fParams = params;
		for (SVDBParamPortDecl p : params) {
			p.setParent(this);
		}
	}

	@Override
	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fParams.add((SVDBParamPortDecl)item);
	}

	@Override
	public ISVDBChildItem getParent() {
		return fParent;
	}

	@Override
	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}

	@Override
	@SuppressWarnings({"unchecked","rawtypes"})
	public Iterable<ISVDBChildItem> getChildren() {
		Iterable it = (Iterable)fParams.iterator();
		return it;
	}
	
	public List<SVDBParamPortDecl> getParams() {
		return fParams;
	}
	
}

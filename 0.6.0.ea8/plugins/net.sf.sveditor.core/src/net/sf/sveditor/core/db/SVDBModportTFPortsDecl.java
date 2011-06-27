package net.sf.sveditor.core.db;


public class SVDBModportTFPortsDecl extends SVDBModportPortsDecl {
	public enum ImpExpType {
		Import,
		Export
	};
	
	private ImpExpType				fImpExpType;
	
	public SVDBModportTFPortsDecl() {
		super(SVDBItemType.ModportTFPortsDecl);
	}
	
	public void setImpExpType(String type) {
		if (type.equals("import")) {
			setImpExpType(ImpExpType.Import);
		} else {
			setImpExpType(ImpExpType.Export);
		}
	}
	
	public void setImpExpType(ImpExpType type) {
		fImpExpType = type;
	}
	
	public ImpExpType getImpExpType() {
		return fImpExpType;
	}

}

package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBConstraint extends SVDBItem {
	private String				fConstraintExpr;
	
	public SVDBConstraint(String name) {
		super(name, SVDBItemType.Constraint);
		fConstraintExpr = "";
	}

	public SVDBConstraint(String name, String expr) {
		super(name, SVDBItemType.Constraint);
		fConstraintExpr = expr;
	}

	public String getConstraintExpr() {
		return fConstraintExpr;
	}
	
	public void setConstraintExpr(String expr) {
		fConstraintExpr = expr;
	}
	
	public SVDBConstraint(
			SVDBFile 		file, 
			SVDBScopeItem 	parent,
			SVDBItemType	type,
			IDBReader		reader) throws DBFormatException {
		super(file, parent, type, reader);
		
		fConstraintExpr = reader.readString();
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fConstraintExpr);
	}
	

}

package net.sf.sveditor.core.db;

/**
 * The class hierarchy object represents an expanded class hierarchy
 * 
 * @author ballance
 *
 */
public class SVDBClassHierarchy extends SVDBModIfcClassDecl {
	
	private SVDBModIfcClassDecl					fOrigClass;
	private SVDBClassHierarchy					fParentClass;
	
	public SVDBClassHierarchy(SVDBModIfcClassDecl orig_class) {
		super(orig_class.getName(), SVDBItemType.Class);
		
		fOrigClass = orig_class;
		super.init(fOrigClass);
	}
	
	public SVDBClassHierarchy getParentClass() {
		return fParentClass;
	}
	
	public void setParentClass(SVDBClassHierarchy parent) {
		fParentClass = parent;
	}
	
}

package net.sf.sveditor.core.db;

public interface IFieldItemAttr {
	int				FieldAttr_Local     = (1 << 0);
	int				FieldAttr_Protected = (1 << 1);
	
	
	void setAttr(int attr);
	
	int getAttr();

}

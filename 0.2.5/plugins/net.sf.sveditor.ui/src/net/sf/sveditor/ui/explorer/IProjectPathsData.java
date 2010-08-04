package net.sf.sveditor.ui.explorer;

public interface IProjectPathsData {
	
	String getName();
	
	Object getParent(Object element);
	
	Object [] getChildren(Object parent);
	

}

package net.sf.sveditor.ui.prop_pages;

import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import net.sf.sveditor.core.db.project.SVProjectFileWrapper;

public interface ISVProjectPropsPage {
	
	String getName();
	
	Image  getIcon();
	
	void init(SVProjectFileWrapper project_wrapper);
	
	Control createContents(Composite parent);
	
	void perfomOk();

}

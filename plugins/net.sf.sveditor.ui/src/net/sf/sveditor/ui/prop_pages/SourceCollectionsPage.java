package net.sf.sveditor.ui.prop_pages;

import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;


public class SourceCollectionsPage implements ISVProjectPropsPage {
	
	private TreeViewer				fSourceCollectionsTree;

	public void init(SVProjectFileWrapper project_wrapper) {
		// TODO Auto-generated method stub
		
	}

	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout(1, true));

		fSourceCollectionsTree = new TreeViewer(frame, SWT.NONE);
		fSourceCollectionsTree.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		return frame;
	}

	public Image getIcon() {
		return SVUiPlugin.getImage("/icons/eview16/source_collection.gif");
	}

	public String getName() {
		return "Source Collections";
	}

	public void perfomOk() {
		// TODO Auto-generated method stub
		
	}
	
}

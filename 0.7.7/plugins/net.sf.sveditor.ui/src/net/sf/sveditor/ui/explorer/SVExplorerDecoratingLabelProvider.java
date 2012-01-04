package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.DecoratingLabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;

public class SVExplorerDecoratingLabelProvider extends DecoratingLabelProvider {
	
	public SVExplorerDecoratingLabelProvider() {
		super(new SVTreeLabelProvider(),
			PlatformUI.getWorkbench().getDecoratorManager().getLabelDecorator());
	}

	@Override
	public Image getImage(Object element) {
		return super.getImage(element);
	}

	
	
}

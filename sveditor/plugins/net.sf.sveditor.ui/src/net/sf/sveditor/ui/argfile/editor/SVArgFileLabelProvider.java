package net.sf.sveditor.ui.argfile.editor;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.ui.ISVIcons;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class SVArgFileLabelProvider extends LabelProvider {

	@Override
	public Image getImage(Object element) {
		if (element instanceof SVDBFileTree) {
			return SVDBIconUtils.getIcon(ISVIcons.ARGFILE);
		}
		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof SVDBFileTree) {
			SVDBFileTree ft = (SVDBFileTree)element;
			return ft.getFilePath();
		}

		return super.getText(element);
	}

}

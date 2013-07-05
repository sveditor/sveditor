package net.sf.sveditor.ui.editor.outline;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class SVOutlineLabelProvider extends LabelProvider {
	private SVDBDecoratingLabelProvider				fBaseLabelProvider;
	
	public SVOutlineLabelProvider() {
		fBaseLabelProvider = new SVDBDecoratingLabelProvider(new SVTreeLabelProvider());
	}

	@Override
	@SuppressWarnings("unchecked")
	public Image getImage(Object element) {
		if (element instanceof SVDBFilePath) {
			return SVUiPlugin.getImage("/icons/eview16/include_hi.png");
		} else if (element instanceof Tuple) {
			Tuple<SVDBFileTree, ISVDBItemBase> t = (Tuple<SVDBFileTree, ISVDBItemBase>)element;
			return fBaseLabelProvider.getImage(t.second());
		} else {
			return fBaseLabelProvider.getImage(element);
		}
	}

	@Override
	@SuppressWarnings("unchecked")
	public String getText(Object element) {
		if (element instanceof SVDBFilePath) {
			return "Include Hierarchy";
		} else if (element instanceof Tuple) {
			// Include-path hierarchy
			Tuple<SVDBFileTree, ISVDBItemBase> it = (Tuple<SVDBFileTree, ISVDBItemBase>)element;
			return SVFileUtils.getPathLeaf(it.first().getFilePath());
		} else {
			return fBaseLabelProvider.getText(element);
		}
	}
	
	

}

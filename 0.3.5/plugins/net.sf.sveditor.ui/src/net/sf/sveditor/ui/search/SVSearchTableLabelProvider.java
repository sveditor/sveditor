package net.sf.sveditor.ui.search;

import java.io.File;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
import org.eclipse.jface.viewers.StyledString;

public class SVSearchTableLabelProvider extends SVTreeLabelProvider implements IStyledLabelProvider {
	
	public SVSearchTableLabelProvider() {
		fShowFunctionRetType = false;
	}
	
	public StyledString getStyledText(Object element) {
		if (element instanceof SVDBItem) {
			StyledString ret = super.getStyledText(element);
			SVDBItem item = (SVDBItem)element;
			SVDBFile file = getFile(item);
			if (file != null) {
				String filename = new File(file.getFilePath()).getName();
				ret.append(" - ");
				ret.append(filename, StyledString.QUALIFIER_STYLER);
//				String decorated = super.getText(element) + " - " + filename;
//				ret.append(" - " + filename);
//				StyledCellLabelProvider.styleDecoratedString(decorated, StyledString.QUALIFIER_STYLER, ret);			
			}
			return ret;
		} else {
			return new StyledString(super.getText(element));
		}
	}

	private static SVDBFile getFile(SVDBItem item) {
		SVDBFile ret = null;
		
		while (item != null) {
			if (item.getType() == SVDBItemType.File) {
				ret = (SVDBFile)item;
				break;
			} else {
				item = (SVDBItem)item.getParent();
			}
		}
		return ret;
	}
	
}

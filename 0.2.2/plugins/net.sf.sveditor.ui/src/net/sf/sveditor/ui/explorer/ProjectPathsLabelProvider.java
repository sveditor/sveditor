package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.swt.graphics.Image;

public class ProjectPathsLabelProvider extends SVTreeLabelProvider {

	@Override
	public Image getImage(Object element) {
		if (element instanceof ProjectPathsData) {
			return SVUiPlugin.getImage("/icons/eview16/project_paths.gif");
		} else if (element instanceof PathTreeNode) {
			return SVUiPlugin.getImage("/icons/eview16/folder.gif");
		} else if (element instanceof LibIndexPath || element instanceof ProjectPathsIndexEntry) {
			String type;
			if (element instanceof LibIndexPath) {
				type = ((LibIndexPath)element).getType();
			} else {
				type = ((ProjectPathsIndexEntry)element).getType();
			}
			if (type.equals(LibIndexPath.TYPE_SRC_COLLECTION)) {
				return SVUiPlugin.getImage("/icons/eview16/source_collection.gif");
			} else if (type.equals(LibIndexPath.TYPE_ARG_FILE) ||
					type.equals(LibIndexPath.TYPE_LIB_PATH)) {
				return SVUiPlugin.getImage("/icons/eview16/sv_lib.gif");
			}
		}
		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof IProjectPathsData) {
			return ((IProjectPathsData)element).getName();
		} else if (element instanceof SVDBFile) {
			return ((SVDBFile)element).getName();
		} else {
			return super.getText(element);
		}
	}
	
	

}

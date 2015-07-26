package net.sf.sveditor.ui.content_providers;

import java.io.File;

import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

public class SVDBFileSystemLabelProvider extends LabelProvider {
	private ISVDBFileSystemProvider				fFS;
	
	public SVDBFileSystemLabelProvider(ISVDBFileSystemProvider fs) {
		fFS = fs;
	}
	
	@Override
	public Image getImage(Object element) {
		if (element instanceof String) {
			ISharedImages imgs = PlatformUI.getWorkbench().getSharedImages();
			
			String path = (String)element;
			if (fFS.isDir(path))  {
				return imgs.getImage(ISharedImages.IMG_OBJ_FOLDER);
			} else {
				IEditorDescriptor editor = PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(path);
				
				if (editor != null) {
					return editor.getImageDescriptor().createImage();
				}

				return imgs.getImage(ISharedImages.IMG_OBJ_FILE);
			}
		}

		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof String) {
			File f = new File((String)element);
			return f.getName();
		} else {
			return super.getText(element);
		}
	}
	

}

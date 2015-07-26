package net.sf.sveditor.ui.content_providers;

import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVDBFileSystemContentProvider implements ITreeContentProvider {
	private ISVDBFileSystemProvider				fFS;

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput instanceof ISVDBFileSystemProvider) {
			fFS = (ISVDBFileSystemProvider)newInput;
		}

	}

	@Override
	public Object[] getElements(Object inputElement) {
		List<String> roots = fFS.getFiles("/");
		
		return roots.toArray();
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		List<String> children = fFS.getFiles((String)parentElement);
		
		return children.toArray();
	}

	@Override
	public Object getParent(Object element) {
		String path = (String)element;
		String ret = null;
		
		if (path.lastIndexOf('/') > 0) {
			ret = path.substring(0, path.lastIndexOf('/'));
		}
		
		return ret;
	}

	@Override
	public boolean hasChildren(Object element) {
		boolean ret = false;
		if (fFS.isDir((String)element)) {
			ret = fFS.getFiles((String)element).size() > 0;
		}
		
		return ret;
	}

}

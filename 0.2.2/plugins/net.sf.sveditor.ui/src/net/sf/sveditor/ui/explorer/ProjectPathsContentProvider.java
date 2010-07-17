package net.sf.sveditor.ui.explorer;

import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.project.SVDBProjectData;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class ProjectPathsContentProvider implements ITreeContentProvider {
	private Map<Object, ProjectPathsData> 		fProjectDataMap;
	private static Object 		NO_ELEMENTS[] = new Object[0];
	
	public ProjectPathsContentProvider() {
		fProjectDataMap = new WeakHashMap<Object, ProjectPathsData>();
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IProject &&
				((IProject)parentElement).getFile(".svproject").exists()) {
			SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(
					(IProject)parentElement);
			if (!fProjectDataMap.containsKey(pd)) {
				fProjectDataMap.put(pd, new ProjectPathsData(pd));
			}
			return new Object[] {fProjectDataMap.get(pd)};
		} else if (parentElement instanceof IProjectPathsData) {
			return ((IProjectPathsData)parentElement).getChildren(parentElement);
		}
		return NO_ELEMENTS;
	}

	public Object getParent(Object element) {
		return null;
	}

	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

	public Object[] getElements(Object inputElement) {
		return NO_ELEMENTS;
	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

}

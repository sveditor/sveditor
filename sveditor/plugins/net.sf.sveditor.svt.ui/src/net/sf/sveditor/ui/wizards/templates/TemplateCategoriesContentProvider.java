package net.sf.sveditor.ui.wizards.templates;

import net.sf.sveditor.svt.core.templates.TemplateCategory;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class TemplateCategoriesContentProvider implements ITreeContentProvider {
	private TemplateCategoriesNode		fRoot;

	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fRoot = (TemplateCategoriesNode)newInput;
	}

	public Object[] getElements(Object inputElement) {
		return fRoot.getCategories().toArray();
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof TemplateCategory) {
			return fRoot.getTemplates((TemplateCategory)parentElement).toArray();
		} else {
			return new Object[0];
		}
	}

	public Object getParent(Object element) {
		
		// TODO Auto-generated method stub
		return null;
	}

	public boolean hasChildren(Object element) {
		return (getChildren(element).length > 0);
	}

}

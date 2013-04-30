package net.sf.sveditor.ui.wizards.templates;

import net.sf.sveditor.svt.core.templates.TemplateCategory;
import net.sf.sveditor.svt.core.templates.TemplateInfo;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class TemplateCategoriesLabelProvider extends LabelProvider {

	@Override
	public Image getImage(Object element) {
		return null;
	}

	@Override
	public String getText(Object element) {
		if (element instanceof TemplateCategory) {
			return ((TemplateCategory)element).getName();
		} else if (element instanceof TemplateInfo) {
			return ((TemplateInfo)element).getName();
		} else {
			return "";
		}
	}

}

package net.sf.sveditor.ui.text.hover;

import org.eclipse.jface.text.DefaultInformationControl;
import org.eclipse.jface.text.IInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Shell;

public class SVDefaultInformationControl extends DefaultInformationControl 
	implements IInformationControlCreator {
	IInformationControlCreator		fCreator;
	Color							fBgColor;
	Color							fFgColor;
	
	public SVDefaultInformationControl(
			Shell 			parent, 
			String 			msg,
			Color			bg_color,
			Color			fg_color) {
		super(parent, msg, new SVDocInformationPresenter());
		setBackgroundColor(bg_color);
		setForegroundColor(fg_color);
		fBgColor = bg_color;
		fFgColor = fg_color;
	}

	@Override
	public IInformationControlCreator getInformationPresenterControlCreator() {
		fCreator = super.getInformationPresenterControlCreator();
		return this;
	}

	public IInformationControl createInformationControl(Shell parent) {
		IInformationControl c = fCreator.createInformationControl(parent);
		if (c instanceof DefaultInformationControl) {
			((DefaultInformationControl)c).setBackgroundColor(fBgColor);
			((DefaultInformationControl)c).setForegroundColor(fFgColor);
		}
		return c;
	}
}
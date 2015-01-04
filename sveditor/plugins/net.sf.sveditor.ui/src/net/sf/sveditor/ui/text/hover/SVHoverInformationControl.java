package net.sf.sveditor.ui.text.hover;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVColorManager;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ToolBarManager;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.text.DefaultInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.IInformationControlExtension2;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;

/**
 * This has a very very very very long description that is unlikely to fit in a hover box. Does it get wrapped? How about now? This is much much much longer now
 * @author ballance
 *
 */
public class SVHoverInformationControl extends DefaultInformationControl 
		implements IInformationControlExtension2, KeyListener {
	IInformationControlCreator						fCreator;
	Color											fBgColor;
	Color											fFgColor;
	private SVHoverInformationControlInput			fInput;
	private ToolBarManager							fToolbarMgr;
	
	private Action									fShowDocAction;
	private Action									fShowDeclInfoAction;
	private Action									fShowMacroExpAction;
	
	public SVHoverInformationControl(Shell parent) {
		super(parent, new ToolBarManager(SWT.FLAT), new SVDocInformationPresenter());
		IPreferenceStore prefs = SVUiPlugin.getDefault().getChainedPrefs();
		Color bg_color = SVColorManager.getColor(PreferenceConverter.getColor(
					prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR));
		Color fg_color = SVColorManager.getColor(PreferenceConverter.getColor(
					prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR));		
		fToolbarMgr = getToolBarManager();
		
		fShowDocAction = new Action("Show Doc", Action.AS_RADIO_BUTTON) {
			public void run() {
				setInformation(fInput.getContent(SVHoverInformationControlInput.CONTENT_DOC));
			}
		};
		fShowDocAction.setImageDescriptor(SVUiPlugin.getImageDescriptor("/icons/edecl16/generate_obj.gif"));
		fToolbarMgr.add(fShowDocAction);

		fShowDeclInfoAction = new Action("Show Declaration", Action.AS_RADIO_BUTTON) {
			public void run() {
				setInformation(fInput.getContent(SVHoverInformationControlInput.CONTENT_DECL));
			}
		};
		fShowDeclInfoAction.setImageDescriptor(SVUiPlugin.getImageDescriptor("/icons/edecl16/public_co.gif"));
		fToolbarMgr.add(fShowDeclInfoAction);
		
		fShowMacroExpAction = new Action("Show Macro Expansion", Action.AS_RADIO_BUTTON) {
			public void run() {
				setInformation(fInput.getContent(SVHoverInformationControlInput.CONTENT_MACRO_EXP));
			}
		};
		fShowMacroExpAction.setImageDescriptor(SVUiPlugin.getImageDescriptor("/icons/edecl16/define_obj.gif"));
		fToolbarMgr.add(fShowMacroExpAction);
		
//		fShowDocAction.setChecked(true);
//		fShowDeclInfoAction.setEnabled(false);
//		fShowMacroExpAction.setEnabled(false);

		setBackgroundColor(bg_color);
		setForegroundColor(fg_color);
		fBgColor = bg_color;
		fFgColor = fg_color;
		
		fToolbarMgr.update(true);
	}
	
	@Override
	public void setInput(Object input) {
		Action actions[] = {
				fShowDocAction,
				fShowDeclInfoAction,
				fShowMacroExpAction
		};
		
		if (input instanceof SVHoverInformationControlInput) {
			fInput = (SVHoverInformationControlInput)input;
		} else {
			fInput = null;
		}
		
		if (fInput != null) {
			int first = -1;
			for (int i=0; i<SVHoverInformationDisplay.fDisplayOrder.length; i++) {
				actions[i].setChecked(false);
				if (fInput.hasContent(SVHoverInformationDisplay.fDisplayOrder[i])) {
					if (first == -1) {
						first = i;
					}
					actions[i].setEnabled(true);
				} else {
					actions[i].setEnabled(false);
				}
			}
			
			if (first != -1) {
				actions[first].setChecked(true);
				setInformation(fInput.getContent(SVHoverInformationDisplay.fDisplayOrder[first]));
			} else {
				setInformation("No Content");
			}
		} else {
			for (Action a : actions) {
				a.setEnabled(false);
			}
		}
	}
	
//	public IInformationControl createInformationControl(Shell parent) {
//		IInformationControl c = fCreator.createInformationControl(parent);
//		if (c instanceof DefaultInformationControl) {
//			((DefaultInformationControl)c).setBackgroundColor(fBgColor);
//			((DefaultInformationControl)c).setForegroundColor(fFgColor);
//			
//
//		}
//
//		return c;
//	}

	@Override
	protected void createContent(Composite parent) {
		super.createContent(parent);
	}

	@Override
	public void keyPressed(KeyEvent e) {
		if (e.keyCode == SWT.TAB) {
			e.doit = false;
		}
		// TODO Auto-generated method stub
		
	}

	@Override
	public void keyReleased(KeyEvent e) {
		if (e.keyCode == SWT.TAB) {
			e.doit = false;
		}
		if (e.keyCode == SWT.TAB) {
			if (fInput != null) {
				setInformation(fInput.next());
			}
		}
		// TODO Auto-generated method stub
		
	}
	
}
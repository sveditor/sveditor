/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.ui.text.hover;

import org.sveditor.ui.SVUiPlugin;
import org.sveditor.ui.editor.SVColorManager;
import org.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.text.DefaultInformationControl;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.IInformationControlExtension2;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.editors.text.EditorsUI;

public class SVHoverInformationDisplay extends DefaultInformationControl 
		implements IInformationControlExtension2 {
	public static final String							fDisplayOrder[] = {
				SVHoverInformationControlInput.CONTENT_DOC,
				SVHoverInformationControlInput.CONTENT_DECL,
				SVHoverInformationControlInput.CONTENT_MACRO_EXP
	};
	
	private SVHoverInformationControlInput				fInput;
	private IInformationControlCreator					fCreator;

	public SVHoverInformationDisplay(Shell parent, IInformationControlCreator creator) {
		super(parent, EditorsUI.getTooltipAffordanceString(), new SVDocInformationPresenter());
		
		fCreator = creator;

		IPreferenceStore prefs = SVUiPlugin.getDefault().getChainedPrefs();
		Color bg_color = SVColorManager.getColor(PreferenceConverter.getColor(
					prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_BG_COLOR));
		Color fg_color = SVColorManager.getColor(PreferenceConverter.getColor(
					prefs, SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_FG_COLOR));
		
		setBackgroundColor(bg_color);
		setForegroundColor(fg_color);
	}
	
	@Override
	public IInformationControlCreator getInformationPresenterControlCreator() {
		return fCreator;
	}

	@Override
	public void setInput(Object input) {
		if (input instanceof SVHoverInformationControlInput) {
			fInput = (SVHoverInformationControlInput)input;
		} else {
			fInput = null;
		}
		
		if (fInput != null) {
			for (int i=0; i<fDisplayOrder.length; i++) {
				if (fInput.hasContent(fDisplayOrder[i])) {
					setInformation(fInput.getContent(fDisplayOrder[i]));
					break;
				}
			}
		}
	}

}

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
package org.eclipse.hdt.sveditor.ui.text.hover;

import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.preproc.ISVStringPreProcessor;

import org.eclipse.hdt.sveditor.ui.editor.SVEditor;

public class SVMacroExpansionHoverContentProvider extends
		SVHoverContentProvider {
	private SVEditor				fEditor;
	private int						fLineno;
	private String					fMacroCall;

	public SVMacroExpansionHoverContentProvider(
			SVEditor 	editor,
			String		macro_call,
			int			lineno) {
		super(null);
		fLog = LogFactory.getLogHandle("SVMacroExpansionHoverContentProvider");
		fLineno = lineno;
		fMacroCall = macro_call;
		fEditor = editor;
	}

	@Override
	public String getContent(SVHoverInformationControlInput input) {
		if (fContent != null) {
			return fContent;
		}

		ISVStringPreProcessor pp2 = fEditor.createPreProcessor(fLineno);
		
		if (pp2 != null) {
			fContent = "";
			fContent += "<b>\n";
//			fContent += "<pre>\n";
			fContent += fMacroCall.trim() + "\n";
//			fContent += "</pre>\n";
			fContent += "</b>\n";
			fContent += "<div/>\n";
			fContent += "<div/>\n";
			fContent += "<pre>\n";
			fContent += "\n\n";
			String tmp = pp2.preprocess(new StringInputStream(fMacroCall));
			tmp = tmp.trim();
			fContent += tmp;
			fContent += "</pre>\n";
			fContent = wrapHTML(fContent);
		} else {
			fContent = "Failed to create preprocessor: " + fMacroCall;
		}
		
		return fContent;
	}
	
	
}

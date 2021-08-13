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

import java.io.IOException;
import java.io.StringReader;

import org.sveditor.ui.doc.HTML2TextReader;

import org.eclipse.jface.text.DefaultInformationControl;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.swt.graphics.Drawable;
import org.eclipse.swt.widgets.Display;

public class SVDocInformationPresenter implements DefaultInformationControl.IInformationPresenter, DefaultInformationControl.IInformationPresenterExtension {

	public String updatePresentation(
			Drawable 			drawable,
			String 				hoverInfo, 
			TextPresentation 	presentation,
			int 				maxWidth, 
			int 				maxHeight) {
		HTML2TextReader rdr = new HTML2TextReader(
				new StringReader(hoverInfo), presentation);
		String ret = hoverInfo;
	
		try {
			ret = rdr.getString();
			rdr.close();
		} catch (IOException e) {}

		return ret;									
	}

	public String updatePresentation(
			Display display, 
			String hoverInfo,
			TextPresentation presentation, 
			int maxWidth, 
			int maxHeight) {
		// TODO Auto-generated method stub
		HTML2TextReader rdr = new HTML2TextReader(
				new StringReader(hoverInfo), presentation);
		String ret = hoverInfo;
		
		try {
			ret = rdr.getString();
			rdr.close();
		} catch (IOException e) {}				
		
		return ret;									
	}
}
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
package org.eclipse.hdt.sveditor.ui.doc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.core.runtime.Platform;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.jface.internal.text.html.HTMLPrinter;
import org.osgi.framework.Bundle;

public class DocUtilUi {
	
	private static String			fgStyleSheet = null;
	private static final LogHandle	fLog = LogFactory.getLogHandle("DocUtilUi");

	/**
	 * Returns the SVDoc hover style sheet 
	 * @return the updated style sheet
	 */
	public static String getStyleSheet() {
		if (fgStyleSheet == null)
			fgStyleSheet= loadStyleSheet();
		String css= fgStyleSheet;
		return css;
	}

	/**
	 * Loads and returns the SVDoc hover style sheet.
	 * @return the style sheet, or <code>null</code> if unable to load
	 */
	private static String loadStyleSheet() {
		Bundle bundle= Platform.getBundle(SVUiPlugin.PLUGIN_ID) ;
		URL styleSheetURL= bundle.getEntry("/SVDocHoverStyleSheet.css"); //$NON-NLS-1$
		if (styleSheetURL != null) {
			BufferedReader reader= null;
			try {
				reader= new BufferedReader(new InputStreamReader(styleSheetURL.openStream()));
				StringBuffer buffer= new StringBuffer(1500);
				String line= reader.readLine();
				while (line != null) {
					buffer.append(line);
					buffer.append('\n');
					line= reader.readLine();
				}
				return buffer.toString();
			} catch (IOException ex) {
				fLog.error("Exception while loading style sheet", ex) ;
				return ""; //$NON-NLS-1$
			} finally {
				try {
					if (reader != null)
						reader.close();
				} catch (IOException e) {
				}
			}
		}
		return null;
	}
	
	public static String formatDoc(String doc) {
		StringBuffer buffer = new StringBuffer(doc);
		
		HTMLPrinter.insertPageProlog(buffer, 0, getStyleSheet());
		HTMLPrinter.addPageEpilog(buffer);
		
		fLog.debug(ILogLevel.LEVEL_MID, 
				"+------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, 
				"| HTML dump") ;
		fLog.debug(ILogLevel.LEVEL_MID,
				buffer.toString()) ;
		fLog.debug(ILogLevel.LEVEL_MID, 
				"+------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, 
				"+------------------------------------------------------------------") ;		
		
		return buffer.toString();
	}
}

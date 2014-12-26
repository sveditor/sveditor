package net.sf.sveditor.ui.text.hover;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;

import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.internal.text.html.HTMLPrinter;
import org.osgi.framework.Bundle;

public class SVHoverContentProvider {
	/**
	 * The style sheet (css).
	 */
	protected static String 		fgStyleSheet;	
	protected String				fContent;
	protected LogHandle				fLog;
	
	public SVHoverContentProvider(String content) {
		fContent = content;
	}

	public String getContent(SVHoverInformationControlInput input) {
		return fContent;
	}
	
	protected String wrapHTML(String content) {
		StringBuffer ret = new StringBuffer();
		
		HTMLPrinter.insertPageProlog(ret, 0, getStyleSheet());
		ret.append(content);
		HTMLPrinter.addPageEpilog(ret);
		
		return ret.toString();
	}

	/**
	 * Returns the SVDoc hover style sheet 
	 * @return the updated style sheet
	 */
	protected String getStyleSheet() {
		if (fgStyleSheet == null)
			fgStyleSheet= loadStyleSheet();
		String css= fgStyleSheet;
		return css;
	}
	
	/**
	 * Loads and returns the SVDoc hover style sheet.
	 * @return the style sheet, or <code>null</code> if unable to load
	 */
	protected String loadStyleSheet() {
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
}


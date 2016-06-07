/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.preproc;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class SVSingleLevelMacroExpander {
	
	private static final boolean		fDebugEn				= false;
	private static final boolean		fDebugChEn				= false;
	private LogHandle					fLog;
	private StringBuilder				fOutput;

	public SVSingleLevelMacroExpander() {
		fLog = LogFactory.getLogHandle("SVSingleLevelMacroExpander");

		fOutput = new StringBuilder();
	}
	
	public String expandMacro(
			SVDBMacroDef	m,
			List<String>	params) {
		fOutput.setLength(0);

		if (m.getParameters() != null && m.getParameters().size() > 0) {
			List<String> param_names = new ArrayList<String>();
			for (SVDBMacroDefParam p : m.getParameters()) {
				param_names.add(p.getName());
			}
			
			expandParameterRefs(new StringTextScanner(m.getDef()), 
					fOutput, param_names, params);
		} else {
			fOutput.append(m.getDef());
		}
	
		return fOutput.toString();
	}
	
	/**
	 * Expand parameter references by name in the identified 
	 * text block
	 * 
	 * @param scanner
	 * @param param_names
	 * @param param_vals
	 */
	private void expandParameterRefs(
			ITextScanner				scanner,
			StringBuilder				out,
			List<String>				param_names,
			List<String>				param_vals) {
		int ch;
		StringBuilder sb = new StringBuilder();

		// Read individual identifiers. Ignore un-escaped strings
		int last_ch = -1;
		while ((ch = scanner.get_ch()) != -1) {
			if (fDebugChEn) {
				debug("  ch=" + (char)ch + " last_ch=" + (char)last_ch);
			}
			if (ch == '"' && last_ch != '`') {
				// un-escaped string
				out.append((char)ch);
				// Skip until the end of this string
				while ((ch = scanner.get_ch()) != -1 && ch != '"' && last_ch != '\\') {
					out.append((char)ch);
					last_ch = ch;
				}
				out.append((char)ch);
				last_ch = ch;
			} else if (ch == '`' && last_ch == '`') {
				// Handle `` as a token separator
				if (fDebugEn) {
					debug("replace ``");
				}
				out.setLength(out.length()-1); // delete the extra '`'
			} else if (Character.isJavaIdentifierStart(ch)) {
				sb.setLength(0);
				ch = AbstractTextScanner.readPreProcIdentifier(sb, scanner, ch);
				last_ch = -1;
				scanner.unget_ch(ch);
			
				String key = sb.toString();

				if (param_names != null && param_vals != null &&
						param_names.size() > 0 && param_vals.size() > 0) {
					int index = param_names.indexOf(key);
					if (index != -1 && index < param_vals.size()) {
						out.append(param_vals.get(index));
					} else {
						out.append(key);
					}
				} else {
					out.append(key);
				}
			} else {
				out.append((char)ch);
				last_ch = ch;
			}
		}

//		if (fDebugEn) {
//			debug("post=" + scanner.getStorage());
//			debug("<-- expandParameterRefs");
//		}
	}
	
	private void debug(String str) {
		if (fDebugEn) {
			fLog.debug(str);
		}
	}

}

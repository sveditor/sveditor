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
package org.eclipse.hdt.sveditor.core.argfile.open_decl;

import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileDefaultOptionProvider;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileExprContext;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileExprScanner;
import org.eclipse.hdt.sveditor.core.argfile.parser.ISVArgFileOptionProvider.OptionType;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.scanutils.IBIDITextScanner;

public class SVArgFileOpenDeclaration {

	public static String openDecl(IBIDITextScanner scanner) {
		SVArgFileDefaultOptionProvider option_provider = new SVArgFileDefaultOptionProvider();
		LogHandle log = LogFactory.getLogHandle("SVargFileOpenDeclaration");
	
		String ret = null;
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, true);
		
		log.debug("ctxt: root=" + ctxt.fRoot + " leaf=" + ctxt.fLeaf);
	
		if (ctxt.fRoot != null) {
			OptionType type = option_provider.getOptionType(ctxt.fRoot);
			if (type == OptionType.ArgFileInc || 
					type == OptionType.ArgFileRootInc ||
					type == OptionType.SrcLibFile) {
				ret = ctxt.fLeaf;
			}
		} else {
			// likely file path
			ret = ctxt.fLeaf;
		}
		
		return ret;
	}
}

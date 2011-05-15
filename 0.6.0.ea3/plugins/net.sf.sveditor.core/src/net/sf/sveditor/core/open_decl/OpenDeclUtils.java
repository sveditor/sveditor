/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.open_decl;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVContentAssistExprVisitor;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.expr_utils.SVExprUtilsParser;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class OpenDeclUtils {
	
	public static List<Tuple<ISVDBItemBase, SVDBFile>> openDecl(
			SVDBFile			file,
			int					line,
			IBIDITextScanner	scanner,
			ISVDBIndexIterator	index_it) {
		LogHandle log = LogFactory.getLogHandle("OpenDeclaration");
//		SVExpressionUtils		expr_utils = new SVExpressionUtils(new SVDBFindDefaultNameMatcher());
		SVExprScanner			expr_scanner = new SVExprScanner();
//		ISVDBItemBase 			it = null;
		SVDBFile 				inc_file = null;
		
		SVExprContext expr_ctxt = expr_scanner.extractExprContext(scanner, true);
		
		log.debug("Expression Context: root=" + expr_ctxt.fRoot +
				" trigger=" + expr_ctxt.fTrigger + " leaf=" + expr_ctxt.fLeaf);
		
		ISVDBScopeItem active_scope = 
			SVDBSearchUtils.findActiveScope(file, line);

		List<Tuple<ISVDBItemBase, SVDBFile>> ret = new ArrayList<Tuple<ISVDBItemBase,SVDBFile>>();

		// If this is an include lookup, then use a different matching strategy
		if (expr_ctxt.fTrigger != null && expr_ctxt.fRoot != null &&
				expr_ctxt.fTrigger.equals("`") && expr_ctxt.fRoot.equals("include")) {
//			expr_utils.setMatcher(new SVDBOpenDeclarationIncludeNameMatcher());
		} else {
			SVExprUtilsParser expr_parser = new SVExprUtilsParser(expr_ctxt, true);
			SVDBExpr expr = null;
			
			try {
				expr = expr_parser.parsers().exprParser().expression();
			} catch (SVParseException e) {
				log.debug("Failed to parse open-declaration expression: " + 
						e.getMessage(), e);
			}

			if (expr != null) {
				SVContentAssistExprVisitor v = new SVContentAssistExprVisitor(
						active_scope, SVDBFindDefaultNameMatcher.getDefault(), index_it);
				ISVDBItemBase item = v.findItem(expr);
				
				if (item != null) {
					ret.add(new Tuple<ISVDBItemBase, SVDBFile>(item, inc_file));
				}
			}
		}

		/*
		List<ISVDBItemBase> items = expr_utils.findItems(index_it, active_scope, expr_ctxt, false);
		
		if (items.size() > 0) {
			it = items.get(0);
			
			// Confused here...
			ret.add(new Tuple<ISVDBItemBase, SVDBFile>(it, inc_file));
		}
		 */
		
		return ret;
	}

}

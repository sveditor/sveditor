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


package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBUtil;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVTaskFunctionParser extends SVParserBase {
	
	public SVTaskFunctionParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse_method_decl(ISVDBScopeItem parent) throws SVParseException {
		parse(parent, -1, true, 0);
	}

	public SVDBTask parse_method_decl() throws SVParseException {
		SVDBScopeItem scope = new SVDBScopeItem();
		parse(scope, -1, true, 0);
		
		return (SVDBTask)SVDBUtil.getFirstChildItem(scope);
	}

	// Enter on 'function'
	public void parse(ISVDBAddChildItem parent, long start, int qualifiers) throws SVParseException {
		parse(parent, start, false, qualifiers);
	}
	
	private void parse(ISVDBAddChildItem parent, long start, boolean is_decl, int qualifiers) throws SVParseException {
		SVDBTask func = null;
		long end = -1;
		String tf_name;
		
		if (start == -1) {
			start = fLexer.getStartLocation();
		}
		
		KW type = fLexer.readKeyword(KW.TASK, KW.FUNCTION);
	
		// ??
		// fLexer.eatToken();
		
		SVDBTypeInfo return_type = null;
		if (type == KW.FUNCTION) {
			if (fLexer.peekKeyword(KW.NEW)) {
				// constructor, so no return type
				tf_name = fLexer.eatTokenR();
				return_type = new SVDBTypeInfoBuiltin("");
			} else {
				if (fLexer.peekKeyword(KW.STATIC, KW.AUTOMATIC)) {
					KW kw = fLexer.readKeywordE();
				// 	TODO: should add this as a qualifier
					if (kw == KW.STATIC) {
						qualifiers |= SVDBFieldItem.FieldAttr_Static;
					}
				}
				
				// data-type or implicit
				List<SVToken> data_type_or_implicit = null;
				if (fLexer.peekKeyword(KW.VOID, KW.VIRTUAL) || 
						SVKeywords.isBuiltInType(fLexer.peek())) {
					data_type_or_implicit = new ArrayList<SVToken>();
					data_type_or_implicit.add(fLexer.consumeToken());
				} else if (fLexer.peekId()) {
					data_type_or_implicit = parsers().SVParser().scopedIdentifier_l(true);
				}
				// Note: data_type_or_implicit could, technically, be null

				if (!fLexer.peekOperator(OP.SEMICOLON, OP.LPAREN) || fLexer.peekOperator(OP.LBRACKET)) {
					// probably data-type or implicit data-type
					// Un-get the tokens we have
					if (data_type_or_implicit != null) {
						fLexer.ungetToken(data_type_or_implicit);
					}
					return_type = parsers().dataTypeParser().data_type_or_void(0);
					tf_name = parsers().SVParser().scopedIdentifier(false);
				} else {
					// function with no return type
					if (data_type_or_implicit != null) {
						tf_name = parsers().SVParser().scopedIdentifierList2Str(data_type_or_implicit);
					} else {
						tf_name = "UNKNOWN";
						error("Task/Function type, name incorrectly parsed");
					}

					// TODO: This is a SystemVerilog warning
				}
			}
		} else {
			// task
			if (fLexer.peekKeyword(KW.STATIC, KW.AUTOMATIC)) {
				// 	TODO: should add this as a qualifier
				KW kw = fLexer.readKeywordE();
				if (kw == KW.STATIC) {
					qualifiers |= SVDBFieldItem.FieldAttr_Static;
				}
			}
			tf_name = parsers().SVParser().scopedIdentifier(false);
		}
		
		List<SVDBParamPortDecl> params = null;
		boolean is_ansi = true;
		if (fDebugEn) {
			debug("Function Terminator: " + fLexer.peek());
		}
		// method declarations are required to have parens
		if (is_decl || fLexer.peekOperator(OP.LPAREN)) {
			// parameter list or empty
			params = parsers().tfPortListParser().parse();
			is_ansi = true;
		} else if (fLexer.peekOperator(OP.SEMICOLON)) {
			// non-ANSI (?)
			params = new ArrayList<SVDBParamPortDecl>();
			is_ansi = false;
		}
		
		// Method declaration is not terminated with a semi-colon
		if (!is_decl) {
			fLexer.readOperator(OP.SEMICOLON);
		}
		
		if (fDebugEn) {
			debug("Procesing " + type + " " + tf_name);
		}
		
		if (type == KW.FUNCTION) {
			func = new SVDBFunction(tf_name, return_type);
		} else {
			func = new SVDBTask(tf_name, SVDBItemType.Task);
		}
		func.setParams(params);
		func.setAttr(qualifiers);
		func.setLocation(start);
	
		debug("TFParse: addChildItem: " + SVDBItem.getName(func) +
				" " + SVDBItem.getName((ISVDBItemBase)parent));
		parent.addChildItem(func);
		
		// Now, parse body items as long as this isn't an extern or pure-virtual method
		if (!is_decl && (qualifiers & SVDBFieldItem.FieldAttr_Extern) == 0 &&
				(qualifiers & (SVDBFieldItem.FieldAttr_Pure|SVDBFieldItem.FieldAttr_Virtual)) !=
					(SVDBFieldItem.FieldAttr_Pure|SVDBFieldItem.FieldAttr_Virtual) &&
				((qualifiers & SVDBFieldItem.FieldAttr_DPI) == 0)) {
			// Parse the body
			try {
				parsers().tfBodyParser().parse(func, is_ansi);
			} catch (SVParseException e) {
				if (fDebugEn) {
					debug("Failed to parse function body", e);
				}
			} finally {
				func.setEndLocation(fLexer.getStartLocation());
			}

			end = fLexer.getStartLocation();
			if  (type == KW.TASK) {
				fLexer.readKeyword(KW.ENDTASK);
			} else {
				fLexer.readKeyword(KW.ENDFUNCTION);
			}

			if (fLexer.peekOperator(OP.COLON)) {
				fLexer.eatToken();
				String id = fLexer.readIdOrKeyword(); // could be :new

				if (!id.equals(func.getName())) {
					// TODO: endfunction label must match function name
				}
			}
		}
		
		if (end == -1) {
			end = fLexer.getStartLocation();
		}
		
		func.setEndLocation(end);
	}

}

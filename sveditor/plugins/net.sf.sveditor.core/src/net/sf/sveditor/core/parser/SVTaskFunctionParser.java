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
import net.sf.sveditor.core.db.SVDBLocation;
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
		parse(parent, null, true, 0);
	}

	public SVDBTask parse_method_decl() throws SVParseException {
		SVDBScopeItem scope = new SVDBScopeItem();
		parse(scope, null, true, 0);
		
		return (SVDBTask)SVDBUtil.getFirstChildItem(scope);
	}

	// Enter on 'function'
	public void parse(ISVDBAddChildItem parent, SVDBLocation start, int qualifiers) throws SVParseException {
		parse(parent, start, false, qualifiers);
	}
	
	private void parse(ISVDBAddChildItem parent, SVDBLocation start, boolean is_decl, int qualifiers) throws SVParseException {
		SVDBTask func = null;
		SVDBLocation end = null;
		String tf_name;
		
		if (start == null) {
			start = fLexer.getStartLocation();
		}
		
		String type = fLexer.readKeyword("task", "function");
	
		// ??
		// fLexer.eatToken();
		
		SVDBTypeInfo return_type = null;
		if (type.equals("function")) {
			if (fLexer.peekKeyword("new")) {
				// constructor, so no return type
				tf_name = fLexer.eatToken();
				return_type = new SVDBTypeInfoBuiltin("");
			} else {
				if (fLexer.peekKeyword("static", "automatic")) {
				// 	TODO: should add this as a qualifier
					if (fLexer.eatToken().equals("static")) {
						qualifiers |= SVDBFieldItem.FieldAttr_Static;
					}
				}
				
				// data-type or implicit
				List<SVToken> data_type_or_implicit = null;
				if (fLexer.peekKeyword("void") || 
						SVKeywords.isBuiltInType(fLexer.peek())) {
					data_type_or_implicit = new ArrayList<SVToken>();
					data_type_or_implicit.add(fLexer.consumeToken());
				} else if (fLexer.peekId()) {
					data_type_or_implicit = parsers().SVParser().scopedIdentifier_l(true);
				}

				if (!fLexer.peekOperator(";", "(") || fLexer.peekOperator("[")) {
					// probably data-type or implicit data-type
					// Un-get the tokens we have
					if (data_type_or_implicit != null) {
						fLexer.ungetToken(data_type_or_implicit);
					}
					return_type = parsers().dataTypeParser().data_type_or_void(0);
					tf_name = parsers().SVParser().scopedIdentifier(false);
				} else {
					// function with no return type
					tf_name = parsers().SVParser().scopedIdentifierList2Str(data_type_or_implicit);

					// TODO: This is a SystemVerilog warning
				}
			}
		} else {
			// task
			if (fLexer.peekKeyword("static", "automatic")) {
				// 	TODO: should add this as a qualifier
				if (fLexer.eatToken().equals("static")) {
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
		if (is_decl || fLexer.peekOperator("(")) {
			// parameter list or empty
			params = parsers().tfPortListParser().parse();
			is_ansi = true;
		} else if (fLexer.peekOperator(";")) {
			// non-ANSI (?)
			params = new ArrayList<SVDBParamPortDecl>();
			is_ansi = false;
		}
		
		// Method declaration is not terminated with a semi-colon
		if (!is_decl) {
			fLexer.readOperator(";");
		}
		
		if (fDebugEn) {
			debug("Procesing " + type + " " + tf_name);
		}
		
		if (type.equals("function")) {
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
			if  (type.equals("task")) {
				fLexer.readKeyword("endtask");
			} else {
				fLexer.readKeyword("endfunction");
			}

			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				String id = fLexer.readIdOrKeyword(); // could be :new

				if (!id.equals(func.getName())) {
					// TODO: endfunction label must match function name
				}
			}
		}
		
		if (end == null) {
			end = fLexer.getStartLocation();
		}
		
		func.setEndLocation(end);
	}

}

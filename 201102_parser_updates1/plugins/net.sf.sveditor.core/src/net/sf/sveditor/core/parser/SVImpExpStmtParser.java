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

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.expr.SVDBStringExpr;
import net.sf.sveditor.core.db.stmt.SVDBExportStmt;
import net.sf.sveditor.core.db.stmt.SVDBImportStmt;

/**
 * Handles both package imports and import DPI statements
 * 
 * @author ballance
 *
 */
public class SVImpExpStmtParser extends SVParserBase {
	
	public SVImpExpStmtParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse_export(ISVDBScopeItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("export");

		if (fLexer.peekString() && 
				(fLexer.peek().equals("DPI") || fLexer.peek().equals("DPI-C"))) {
			fLexer.eatToken();
			parse_dpi_tf(parent, start);
		} else {
			SVDBExportStmt exp = new SVDBExportStmt();
			exp.setLocation(start);
			if (fLexer.peekOperator("*")) {
				
				fLexer.startCapture();
				fLexer.readOperator("*");
				fLexer.readOperator("::");
				fLexer.readOperator("*");
				exp.addExport(new SVDBStringExpr(fLexer.endCapture()));
			} else {
				
				while (fLexer.peek() != null) {
					exp.addExport(package_import_item());
					
					if (fLexer.peekOperator(",")) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
			}
			fLexer.readOperator(";");
			parent.addItem(exp);
		}
	}
	
	private void parse_dpi_tf(ISVDBScopeItem parent, SVDBLocation start) throws SVParseException {
		int modifiers = IFieldItemAttr.FieldAttr_DPI;

		modifiers |= parsers().SVParser().scan_qualifiers(false);
		
		if (fLexer.peekId()) {
			// c_identifier =
			// TODO: capture?
			fLexer.readId();
			fLexer.readOperator("=");
		}

		// Read tf extern declaration
		parsers().taskFuncParser().parse(parent, start, modifiers);
	}

	public void parse_import(ISVDBScopeItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("import");
		
		if (fLexer.peekString()) {
			// likely DPI import/export. Double-check
			String qualifier = fLexer.readString();

			if (qualifier != null && qualifier.equals("DPI")
					|| qualifier.equals("DPI-C")) {
				parse_dpi_tf(parent, start);
			} else {
				error("Expecting DPI import, but received \"" + qualifier + "\"");
			}
		} else {
			SVDBImportStmt imp = new SVDBImportStmt();
			imp.setLocation(start);
			while (fLexer.peek() != null) {
				imp.addImport(package_import_item());
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		
			fLexer.readOperator(";");
			parent.addItem(imp);
		}
	}
	
	private SVDBStringExpr package_import_item() throws SVParseException {
		fLexer.startCapture();
		fLexer.readId();
		while (fLexer.peekOperator("::")) {
			fLexer.eatToken();
			if (fLexer.peekOperator("*")) {
				fLexer.eatToken();
			} else {
				fLexer.readId();
			}
		}
		
		return new SVDBStringExpr(fLexer.endCapture());
	}
}

/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.parser;

import org.eclipse.hdt.sveditor.core.db.IFieldItemAttr;
import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBExportItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBExportStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBImportItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBImportStmt;

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
	
	public void parse_export(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		fLexer.readKeyword(KW.EXPORT);

		if (fLexer.peekString() && 
				(fLexer.peek().equals("DPI") || fLexer.peek().equals("DPI-C"))) {
			fLexer.eatToken();
			parse_dpi_tf(parent, start);
		} else {
			SVDBExportStmt exp = new SVDBExportStmt();
			exp.setLocation(start);
			if (fLexer.peekOperator(OP.MUL)) {
				SVStringTokenListener l = new SVStringTokenListener();
				SVDBExportItem ei = new SVDBExportItem();
				fLexer.addTokenListener(l);
				try {
					fLexer.readOperator(OP.MUL);
					fLexer.readOperator(OP.COLON2);
					fLexer.readOperator(OP.MUL);
				} finally {
					fLexer.removeTokenListener(l);
				}
				ei.setExport(l.toString());
				exp.addChildItem(ei);
			} else {
				
				while (fLexer.peek() != null) {
					exp.addChildItem(package_export_item());
					
					if (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
					} else {
						break;
					}
				}
			}
			fLexer.readOperator(OP.SEMICOLON);
			parent.addChildItem(exp);
		}
	}
	
	private void parse_dpi_tf(ISVDBAddChildItem parent, long start) throws SVParseException {
		int modifiers = IFieldItemAttr.FieldAttr_DPI;

		modifiers |= parsers().SVParser().scan_qualifiers(false);
		
		if (fLexer.peekId()) {
			// c_identifier =
			// TODO: capture?
			fLexer.readId();
			fLexer.readOperator(OP.EQ);
		}

		// Read tf extern declaration
		parsers().taskFuncParser().parse(parent, start, modifiers);
	}

	public void parse_import(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		fLexer.readKeyword(KW.IMPORT);
		
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
				imp.addChildItem(package_import_item());
				
				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		
			fLexer.readOperator(OP.SEMICOLON);
			parent.addChildItem(imp);
		}
	}
	
	private SVDBImportItem package_import_item() throws SVParseException {
		SVDBImportItem imp = new SVDBImportItem();
		imp.setLocation(fLexer.getStartLocation());
		SVStringTokenListener l = new SVStringTokenListener();
		fLexer.addTokenListener(l);
		try {
			fLexer.readId();
			while (fLexer.peekOperator(OP.COLON2)) {
				fLexer.eatToken();
				if (fLexer.peekOperator(OP.MUL)) {
					fLexer.eatToken();
				} else {
					fLexer.readId();
				}
			}
		} finally {
			fLexer.removeTokenListener(l);
		}
		imp.setImport(l.toString());
		return imp;
	}
	
	private SVDBExportItem package_export_item() throws SVParseException {
		SVDBExportItem exp = new SVDBExportItem();
		exp.setLocation(fLexer.getStartLocation());
		SVStringTokenListener l = new SVStringTokenListener();
		fLexer.addTokenListener(l);
		try {
			fLexer.readId();
			while (fLexer.peekOperator(OP.COLON2)) {
				fLexer.eatToken();
				if (fLexer.peekOperator(OP.MUL)) {
					fLexer.eatToken();
				} else {
					fLexer.readId();
				}
			}
		} finally {
			fLexer.removeTokenListener(l);
		}
		exp.setExport(l.toString());
		return exp;
	}
}

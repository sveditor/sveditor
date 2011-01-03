package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.SVDBImport;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;

/**
 * Handles both package imports and import DPI statements
 * 
 * @author ballance
 *
 */
public class SVImportStmtParser extends SVParserBase {
	
	public SVImportStmtParser(ISVParser parser) {
		super(parser);
	}

	public List<SVDBItem> parse() throws SVParseException {
		List<SVDBItem> imports = new ArrayList<SVDBItem>();
		
		SVDBLocation start = lexer().getStartLocation();
		lexer().readKeyword("import");
		
		if (lexer().peekString()) {
			// likely DPI import/export. Double-check
			String qualifier = lexer().readString();

			if (qualifier != null && qualifier.equals("DPI")
					|| qualifier.equals("DPI-C")) {
				int modifiers = IFieldItemAttr.FieldAttr_DPI;

				modifiers |= parsers().SVParser().scan_qualifiers(false);

				// Read tf extern declaration
				SVDBTaskFuncScope tf = parsers().functionParser().parse(start, modifiers);
				imports.add(tf);
			}
		} else {
			while (lexer().peek() != null) {
				lexer().startCapture();
				lexer().readId();
				while (lexer().peekOperator("::")) {
					lexer().eatToken();
					if (lexer().peekOperator("*")) {
						lexer().eatToken();
					} else {
						lexer().readId();
					}
				}
				
				String imp_expr = lexer().endCapture();
				SVDBImport imp_item = new SVDBImport(imp_expr);
				imp_item.setLocation(start);
				imports.add(imp_item);
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		
			lexer().readOperator(";");
		}
		
		return imports;
	}
}

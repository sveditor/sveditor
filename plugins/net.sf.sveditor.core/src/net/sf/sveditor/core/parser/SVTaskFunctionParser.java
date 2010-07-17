package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVTaskFunctionParser extends SVParserBase {
	
	public SVTaskFunctionParser(ISVParser parser) {
		super(parser);
	}
	
	// Enter on 'function'
	public SVDBTaskFuncScope parse(SVDBLocation start, int qualifiers) throws SVParseException {
		SVDBTaskFuncScope func = null;
		SVDBLocation end = null;
		String tf_name;
		
		if (start == null) {
			start = lexer().getStartLocation();
		}
		
		String type = lexer().readKeyword("task", "function");
	
		// ??
		// lexer().eatToken();
		
		SVDBTypeInfo return_type = null;
		if (type.equals("function")) {
			if (lexer().peekKeyword("new")) {
				// constructor, so no return type
				tf_name = lexer().eatToken();
				return_type = new SVDBTypeInfoBuiltin("");
			} else {
				if (lexer().peekKeyword("static", "automatic")) {
				// 	TODO: should add this as a qualifier
					if (lexer().eatToken().equals("static")) {
						qualifiers |= SVDBFieldItem.FieldAttr_Static;
					}
				}
			
				// data-type or implicit
				String data_type_or_implicit;
				if (lexer().peekKeyword("void") || 
						SVKeywords.isBuiltInType(lexer().peek())) {
					data_type_or_implicit = lexer().eatToken();
				} else {
					data_type_or_implicit = parsers().SVParser().scopedIdentifier(true);
				}

				if (!lexer().peekOperator(";", "(")) {
					// probably data-type
					return_type = parsers().dataTypeParser().data_type_or_void(0, data_type_or_implicit);
					tf_name = parsers().SVParser().scopedIdentifier(false);
				} else {
					// function with no return type
					tf_name = data_type_or_implicit;

					// TODO: This is a SystemVerilog warning
				}
			}
		} else {
			// task
			if (lexer().peekKeyword("static", "automatic")) {
				// 	TODO: should add this as a qualifier
				if (lexer().eatToken().equals("static")) {
					qualifiers |= SVDBFieldItem.FieldAttr_Static;
				}
			}
			tf_name = parsers().SVParser().scopedIdentifier(false);
		}
		
		List<SVDBParamPort> params = null;
		boolean is_ansi = true;
		if (lexer().peekOperator("(")) {
			// parameter list or empty
			params = parsers().tfPortListParser().parse();
			is_ansi = true;
		} else if (lexer().peekOperator(";")) {
			// non-ANSI (?)
			params = new ArrayList<SVDBParamPort>();
			is_ansi = false;
		}
		lexer().readOperator(";");
		
		if (type.equals("function")) {
			func = new SVDBTaskFuncScope(tf_name, return_type);
		} else {
			func = new SVDBTaskFuncScope(tf_name, SVDBItemType.Task);
		}
		func.setParams(params);
		func.setAttr(qualifiers);
		func.setLocation(start);
		
		// Now, parse body items as long as this isn't an extern or pure-virtual method
		if ((qualifiers & SVDBFieldItem.FieldAttr_Extern) == 0 &&
				(qualifiers & (SVDBFieldItem.FieldAttr_Pure|SVDBFieldItem.FieldAttr_Virtual)) !=
					(SVDBFieldItem.FieldAttr_Pure|SVDBFieldItem.FieldAttr_Virtual) &&
				((qualifiers & SVDBFieldItem.FieldAttr_DPI) == 0)) {
			// Parse the body
			parsers().tfBodyParser().parse(func, is_ansi);
		
			end = lexer().getStartLocation();
			if  (type.equals("task")) {
				lexer().readKeyword("endtask");
			} else {
				lexer().readKeyword("endfunction");
			}
			
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				String id = lexer().readIdOrKeyword(); // could be :new
				
				if (!id.equals(func.getName())) {
					// TODO: endfunction label must match function name
				}
			}
		}
		
		if (end == null) {
			end = lexer().getStartLocation();
		}
		
		func.setEndLocation(end);
		
		return func;
	}

}

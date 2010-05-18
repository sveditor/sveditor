package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class SVFunctionParser extends SVParserBase {
	
	public SVFunctionParser(ISVParser parser) {
		super(parser);
	}
	
	// Enter on 'function'
	public SVDBTaskFuncScope parse(int qualifiers) throws SVParseException {
		SVDBTaskFuncScope func = null;
		String tf_name;
		
		lexer().readKeyword("function");
		
		lexer().next_token();
		
		SVDBTypeInfo return_type = null;
		if (lexer().peekKeyword("new")) {
			// constructor, so no return type
			tf_name = lexer().eatToken();
			return_type = new SVDBTypeInfo("", 0);
		} else {
			if (lexer().peekKeyword("static", "automatic")) {
				// TODO: should add this as a qualifier
				if (lexer().eatToken().equals("static")) {
					qualifiers |= SVDBFieldItem.FieldAttr_Static;
				}
			}
			
			// data-type or implicit
			String data_type_or_implicit;
			if (lexer().peekKeyword("void")) {
				data_type_or_implicit = lexer().eatToken();
			} else {
				data_type_or_implicit = parsers().SVParser().scopedIdentifier();
			}
			
			if (!lexer().peekOperator(";", "(")) {
				// probably data-type
				return_type = parsers().dataTypeParser().data_type_or_void(data_type_or_implicit);
				tf_name = lexer().readId();
			} else {
				// function with no return type
				tf_name = data_type_or_implicit;
				
				// TODO: This is a SystemVerilog warning
			}
		}
		
		List<SVDBTaskFuncParam> params = null;
		boolean is_ansi = true;
		if (lexer().peekOperator("(")) {
			// parameter list or empty
			params = parsers().tfPortListParser().parse();
			is_ansi = true;
		} else if (lexer().peekOperator(";")) {
			// non-ANSI (?)
			params = new ArrayList<SVDBTaskFuncParam>();
			is_ansi = false;
		}
		lexer().readOperator(";");
		
		func = new SVDBTaskFuncScope(tf_name, return_type);
		func.setParams(params);
		func.setAttr(qualifiers);
		
		// Now, parse body items as long as this isn't an extern or pure-virtual method
		if ((qualifiers & SVDBFieldItem.FieldAttr_Extern) == 0 &&
				(qualifiers & (SVDBFieldItem.FieldAttr_Pure|SVDBFieldItem.FieldAttr_Virtual)) !=
					(SVDBFieldItem.FieldAttr_Pure|SVDBFieldItem.FieldAttr_Virtual)) {
			// Parse the body
			parsers().tfBodyParser().parse(func, is_ansi);
			
			lexer().readKeyword("endfunction");
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				String id = lexer().readId();
				
				if (!id.equals(func.getName())) {
					// TODO: endfunction label must match function name
				}
			}
		}
		
		
		return func;
	}

}

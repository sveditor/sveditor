package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;

public class SVClassDeclParser extends SVParserBase {
	
	public SVClassDeclParser(ISVParser parser) {
		super(parser);
	}
	
	/**
	 * 
	 * [ virtual ] class [ lifetime ] class_identifier [ parameter_port_list ]
	 * [ extends class_type [ ( list_of_arguments ) ] ];
	 * @param qualifiers
	 * @return
	 * @throws SVParseException
	 */
	public SVDBModIfcClassDecl parse(int qualifiers) throws SVParseException {
		SVDBModIfcClassDecl cls = null;
		String id;
		String cls_type_name = null;
		
		debug("--> process_class()");
		
		// Expect to enter on 'class'
		lexer().readKeyword("class");
		
		if (lexer().peekKeyword("automatic", "static")) {
			// TODO: set lifetime on class declaration
			lexer().eatToken();
		}

		//
		// Class ID
		//
		cls_type_name = parsers().SVParser().scopedIdentifier(
				((qualifiers & IFieldItemAttr.FieldAttr_SvBuiltin) != 0));
		
		cls = new SVDBModIfcClassDecl(cls_type_name, SVDBItemType.Class);
		
		// TODO: Should remove this later
		parsers().SVParser().enter_scope("class", cls);
		
		if (lexer().peekOperator("#")) {
			// Handle classes with parameters
			cls.getParameters().addAll(parsers().paramPortListParser().parse());
		}
		
		if (lexer().peekKeyword("extends")) {
			lexer().eatToken();
			cls.setSuperClass(lexer().readId());

			if (lexer().peekOperator("#")) {
				// scanner().unget_ch('#');
				// TODO: List<SVDBModIfcClassParam> params = fParamDeclParser.parse();
				// cls.getSuperParameters().addAll(params);
				lexer().eatToken();
				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				} else {
					lexer().eatToken();
				}
			}
		}
		
		lexer().readOperator(";");
		
		// Force new-statement
		parsers().SVParser().setNewStatement();
		
		// TODO: need a better system here...
		while ((id = parsers().SVParser().scan_statement()) != null) {
			SVDBItem item;
			if (id.equals("endclass")) {
				break;
			}
			
			item = parsers().SVParser().process_module_class_interface_body_item("class", id);

			// Check whether we aborted parsing the body because
			// we found a 1st-level scope keyword
			if (item == null) {
				break;
			}
			
			// TODO: normally we'd add this item to the class, but that's already being done
		}

		if (lexer().peekKeyword("endclass")) {
			lexer().eatToken();
			// endclass : classname
			if (lexer().peekOperator(":")) { 
				lexer().eatToken();
				lexer().readId();
			}
		}
		
		// TODO: remove this later
		parsers().SVParser().handle_leave_scope();
		
		return cls;
	}

}

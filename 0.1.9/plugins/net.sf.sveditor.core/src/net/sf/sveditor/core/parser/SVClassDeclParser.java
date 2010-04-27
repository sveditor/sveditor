package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;
import net.sf.sveditor.core.scanutils.ITextScanner;

public class SVClassDeclParser extends SVParserBase {
	private ITextScanner				fScanner;
	private SVParameterDeclParser		fParamDeclParser;
	
	public SVClassDeclParser(SVLexer lexer, ITextScanner scanner) {
		super(lexer);
		fScanner = scanner;
		fParamDeclParser 	= new SVParameterDeclParser(lexer);
	}
	
	public SVDBModIfcClassDecl parse(int qualifiers) throws SVParseException {
		SVDBModIfcClassDecl cls = null;
		String id;
		List<SVClassIfcModParam>	params = null;
		String super_name = null;
		List<SVClassIfcModParam>	super_params = null;
		String cls_type_name = null;
		String ports = null;
		
		debug("--> process_module()");

		//
		// Class ID
		//
		cls_type_name = fLexer.readId();
		
		cls = new SVDBModIfcClassDecl(cls_type_name, SVDBItemType.Class);

		if (fLexer.peekOperator("#")) {
			// Handle classes with parameters
			cls.getParameters().addAll(fParamDeclParser.parse());
		}
		/*
		ch = skipWhite(ch);
		if (ch == '#') {
			ch = skipWhite(get_ch());
			if (ch == '(') {
				startCapture();
				ch = skipPastMatch("()");
				String p_str = endCapture();
				
				params = parse_parameter_str(p_str);
			}
		}
		 */
		
		if (params == null) {
			params = new ArrayList<SVClassIfcModParam>();
		}
		
		if (fLexer.peekKeyword("extends")) {
			String ext = fLexer.readId();
			cls.setSuperClass(ext);

			if (fLexer.peekOperator("#")) {
				
				// TODO: super-class parameterization ?
				/*
				for (SVClassIfcModParam p : super_params) {
					decl.getSuperParameters().add(new SVDBModIfcClassParam(p.getName()));
				}
				 */
			}
		}
		
		fLexer.readOperator(";");
		/*
		while ((id = scan_statement()) != null) {
			boolean ret;
			debug("id=" + id);
			if (id.equals("end" + type)) {
				break;
			}
			ret = process_module_class_interface_body_item(type, id);

			// Check whether we aborted parsing the body because
			// we found a 1st-level scope keyword
			if (!ret) {
				break;
			}
		}
		
		// Pop the first-level scope
		handle_leave_scope();
		 */
		
		return cls;
	}

}

package net.sf.sveditor.core.parser;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltinNet;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt.AlwaysType;
import net.sf.sveditor.core.db.stmt.SVDBBodyStmt;
import net.sf.sveditor.core.db.stmt.SVDBFinalStmt;
import net.sf.sveditor.core.db.stmt.SVDBInitialStmt;
import net.sf.sveditor.core.db.stmt.SVDBNullStmt;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVModIfcBodyItemParser extends SVParserBase {
	private final ISVDBChildItem fSpecialNonNull = new SVDBNullStmt();
	
	public SVModIfcBodyItemParser(ISVParser parser) {
		super(parser);
	}
	
	public ISVDBChildItem parse(String typename) throws SVParseException {
		int modifiers = 0;
		ISVDBChildItem ret = null;
		String id = fLexer.peek();

		debug("--> process_module_class_interface_body_item: \"" + id + 
				"\" @ " + fLexer.getStartLocation().getLine());

		// Save the start location before qualifiers
		SVDBLocation start = fLexer.getStartLocation();
		modifiers = parsers().SVParser().scan_qualifiers(false);

		id = fLexer.peek();

		debug("body item is: " + id);

		if (id.equals("function") || id.equals("task")) {
			ret = parsers().taskFuncParser().parse(start, modifiers);
		} else if (id.equals("property")) {
			ret = parsers().SVParser().process_property();
		} else if (fLexer.peekKeyword("generate", "for", "if", "case")) {
			// Generate-block statements
			ret = parsers().generateBlockParser().parse();
		} else if (id.equals("specify")) {
			ret = parsers().specifyBlockParser().parse();
		} else if (fLexer.peekKeyword("default", "global", "clocking")) {
			// Clocking block
			ret = parsers().clockingBlockParser().parse();
		} else if (id.equals(";")) {
			// null statement
			fLexer.eatToken();
			ret = new SVDBNullStmt();
		} else if (fLexer.peekKeyword("always","always_comb","always_latch","always_ff","initial")) {
			ret = parse_initial_always();
		} else if (fLexer.peekKeyword("final")) {
			ret = parse_final();
		} else if (id.equals("modport")) {
			// TODO: shouldn't just skip
			fLexer.eatToken();
			fLexer.readId(); // modport name
			
			fLexer.skipPastMatch("(", ")");
			fLexer.readOperator(";");
			ret = fSpecialNonNull;
		} else if (id.equals("assign")) {
			ret = parse_assign();
		} else if (id.equals("covergroup")) {
			ret = parsers().covergroupParser().parse();
		} else if (id.equals("constraint")) {
			ret = fParsers.constraintParser().parse(modifiers);
		} else if (id.equals("sequence")) {
			fParsers.SVParser().process_sequence();
			ret = fSpecialNonNull;
		} else if (id.equals("import")) {
			ret = parsers().impExpParser().parse_import();
		} else if (id.equals("clocking")) {
			ret = fParsers.clockingBlockParser().parse();
		} else if (id.equals("typedef")) {
			SVDBTypedefStmt td = parsers().dataTypeParser().typedef();
			
			ret = td;
		} else if (id.equals("class")) {
			SVDBClassDecl cls = null;
			try {
				cls = parsers().classParser().parse(modifiers);
			} catch (SVParseException e) {
//				System.out.println("ParseException: post-class-module()");
//				e.printStackTrace();
			}
			ret = cls;
		} else if (id.equals("module") || id.equals("program") ||
				(id.equals("interface") && (modifiers & SVDBFieldItem.FieldAttr_Virtual) == 0)) {
			SVDBModIfcDecl m = null;
			// enter module scope
			// TODO: should probably add this item to the 
			// File scope here
			try {
				m = parsers().modIfcProgParser().parse(modifiers);
			} catch (SVParseException e) {
			}
			
			ret = m;
		} else if (id.equals("parameter") || id.equals("localparam")) {
			// local parameter
			fLexer.eatToken();
			
			if (fLexer.peekKeyword("type")) {
				fLexer.eatToken();
			}
			SVDBTypeInfo data_type = parsers().dataTypeParser().data_type(0);
			String param_name;
			
			SVDBLocation it_start = fLexer.getStartLocation();
			
			if (fLexer.peekId()) {
				// likely a typed parameter
				param_name = fLexer.readId();
			} else {
				// likely an untyped parameter
				param_name = data_type.getName();
				data_type = null;
			}
			
			SVDBParamPortDecl p = new SVDBParamPortDecl(data_type);
			SVDBVarDeclItem pi;
			while (true) {
				if (fLexer.peekOperator("=")) {
					fLexer.eatToken();
					parsers().exprParser().expression();
				}
				
				pi = new SVDBVarDeclItem(param_name);
				pi.setLocation(it_start);
				p.addVar(pi);
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					it_start = fLexer.getStartLocation();
					param_name = fLexer.readId();
				} else {
					break;
				}
			}
			fLexer.readOperator(";");
			ret = fSpecialNonNull;
		} else if (SVDataTypeParser.NetType.contains(id)) {
			ret = parse_var_decl();
		} else if (fLexer.peekKeyword(SVKeywords.fBuiltinGates)) {
			List<SVDBModIfcInst> insts = parsers().gateInstanceParser().parse();
			// TODO: add to hierarchy (?)
			ret = fSpecialNonNull;
		} else if (fLexer.peekKeyword("defparam", "specparam")) {
			// TODO: defparam doesn't appear in hierarchy
			fLexer.eatToken();
			while (fLexer.peek() != null && !fLexer.peekOperator(";")) {
				parsers().exprParser().expression();
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			fLexer.readOperator(";");
		} else if (!fLexer.peekOperator()) {
			// likely a variable or module declaration

			debug("Likely VarDecl: " + id);

			fParsers.SVParser().scanVariableDeclaration(modifiers);
			ret = fSpecialNonNull;
		}

		debug("<-- process_module_class_interface_body_item - " + 
				((ret != null)?SVDBItem.getName(ret):"NULL"));

		if (ret != null) {
			ret.setLocation(start);
		}
		return ret;
	}
	
	public SVDBAssign parse_assign() throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("assign");
		SVDBAssign assign = new SVDBAssign();
		assign.setLocation(start);
		
		if (fLexer.peekOperator("#")) {
			// Time expression
			assign.setDelay(fParsers.exprParser().delay_expr());
		}
		
		assign.setLHS(fParsers.exprParser().variable_lvalue());
		
		fLexer.readOperator("=");
		
		assign.setRHS(fParsers.exprParser().expression());
		
		fLexer.readOperator(";");
		
		return assign;
	}
	
	private SVDBVarDeclStmt parse_var_decl() throws SVParseException {
		// net type
		String net_type = fLexer.eatToken();
		String vector_dim = null;
		SVDBVarDeclStmt var = null;
		String net_name = null;
		SVDBLocation start = null;
		SVDBTypeInfoBuiltinNet type_info = null;
		SVDBTypeInfo data_type = null;
		
		debug("Net Type: " + net_type + " @ " + 
				fLexer.getStartLocation().getLine());
		
		// vectored untyped net
		if (fLexer.peekOperator("[")) {
			// TODO:
			data_type = new SVDBTypeInfoBuiltin(net_type);
			fLexer.startCapture();
			fLexer.skipPastMatch("[", "]");
			vector_dim = fLexer.endCapture();
			((SVDBTypeInfoBuiltin)data_type).setVectorDim(vector_dim);
			start = fLexer.getStartLocation();
			net_name = fLexer.readId();
		} else {
			data_type = parsers().dataTypeParser().data_type(0);

			// Now, based on what we see next, we determine whether the
			// net is typed or untyped

			if (fLexer.peekOperator(",", ";", "=")) {
				// The net was untyped
				start = fLexer.getStartLocation();
				net_name = data_type.getName();
				data_type = new SVDBTypeInfoBuiltin(net_type);
			} else {
				// Assume the net to be typed
				start = fLexer.getStartLocation();
				net_name = fLexer.readId();
			}
		}
		type_info = new SVDBTypeInfoBuiltinNet(net_type, data_type);
		
		var = new SVDBVarDeclStmt(type_info, 0);
		while (true) {
			
			SVDBVarDeclItem vi = new SVDBVarDeclItem(net_name);
			vi.setLocation(start);
			var.addVar(vi);
			
			if (fLexer.peekOperator("[")) {
				vi.setArrayDim(parsers().dataTypeParser().var_dim());
			}
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				start = fLexer.getStartLocation();
				net_name = fLexer.readId();
			} else if (fLexer.peekOperator("=")) {
				// Initialized wire
				fLexer.eatToken();
				parsers().exprParser().expression();
			} else {
				break;
			}
		}
		
		fLexer.readOperator(";");
		return var;
	}
	
	private ISVDBChildItem parse_final() throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("final");
		
		SVDBBodyStmt ret = new SVDBFinalStmt();
		ret.setLocation(start);
		
		ret.setBody(fParsers.behavioralBlockParser().statement());
		
		return ret;
	}

	private ISVDBChildItem parse_initial_always() throws SVParseException {
		ISVDBChildItem ret = null;
		SVDBLocation start = fLexer.getStartLocation();
		String type = fLexer.readKeyword("initial", 
				"always", "always_comb", "always_latch", "always_ff");

		if (!type.equals("initial")) { // always
			AlwaysType always_type = null;
			
			if (type.equals("always")) {
				always_type = AlwaysType.Always;
			} else if (type.equals("always_comb")) {
				always_type = AlwaysType.AlwaysComb;
			} else if (type.equals("always_latch")) {
				always_type = AlwaysType.AlwaysLatch;
			} else if (type.equals("always_ff")) {
				always_type = AlwaysType.AlwaysFF;
			}
			ret = new SVDBAlwaysStmt(always_type);
		} else {
			ret = new SVDBInitialStmt();
		}
		ret.setLocation(start);
		
		((SVDBBodyStmt)ret).setBody(fParsers.behavioralBlockParser().statement());

		return ret;
	}
}

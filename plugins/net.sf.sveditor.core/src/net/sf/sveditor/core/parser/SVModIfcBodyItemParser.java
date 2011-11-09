/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBModportClockingPortDecl;
import net.sf.sveditor.core.db.SVDBModportDecl;
import net.sf.sveditor.core.db.SVDBModportItem;
import net.sf.sveditor.core.db.SVDBModportPortsDecl;
import net.sf.sveditor.core.db.SVDBModportSimplePort;
import net.sf.sveditor.core.db.SVDBModportSimplePortsDecl;
import net.sf.sveditor.core.db.SVDBModportTFPort;
import net.sf.sveditor.core.db.SVDBModportTFPortsDecl;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltinNet;
import net.sf.sveditor.core.db.SVDBTypeInfoModuleIfc;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt.AlwaysEventType;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt.AlwaysType;
import net.sf.sveditor.core.db.stmt.SVDBBodyStmt;
import net.sf.sveditor.core.db.stmt.SVDBDefParamItem;
import net.sf.sveditor.core.db.stmt.SVDBDefParamStmt;
import net.sf.sveditor.core.db.stmt.SVDBFinalStmt;
import net.sf.sveditor.core.db.stmt.SVDBInitialStmt;
import net.sf.sveditor.core.db.stmt.SVDBNullStmt;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBTimePrecisionStmt;
import net.sf.sveditor.core.db.stmt.SVDBTimeUnitsStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVModIfcBodyItemParser extends SVParserBase {
	
	public SVModIfcBodyItemParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent, String typename) throws SVParseException {
		int modifiers = 0;
		if (fLexer.peekOperator("(*")) {
			fParsers.attrParser().parse(parent);
		}
		String id = fLexer.peek();

		debug("--> process_module_class_interface_body_item: \"" + id + 
				"\" @ " + fLexer.getStartLocation().getLine());

		// Save the start location before qualifiers
		SVDBLocation start = fLexer.getStartLocation();
		modifiers = parsers().SVParser().scan_qualifiers(false);

		id = fLexer.peek();

		debug("body item is: " + id);

		if (id.equals("function") || id.equals("task")) {
			parsers().taskFuncParser().parse(parent, start, modifiers);
		} else if (fLexer.peekKeyword("assert","assume","cover","restrict")) {
			parsers().assertionParser().parse(parent);
		} else if (id.equals("property")) {
			fParsers.propertyParser().property(parent);
		} else if (fLexer.peekKeyword("generate", "for", "if", "case")) {
			// Generate-block statements
			parsers().generateBlockParser().parse(parent);
		} else if (id.equals("specify")) {
			parsers().specifyBlockParser().parse(parent);
		} else if (fLexer.peekKeyword("default", "global", "clocking")) {
			// Clocking block
			parsers().clockingBlockParser().parse(parent);
		} else if (id.equals(";")) {
			// null statement
			SVDBNullStmt stmt = new SVDBNullStmt();
			stmt.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
			parent.addChildItem(stmt);
		} else if (fLexer.peekKeyword("always","always_comb","always_latch","always_ff","initial")) {
			parse_initial_always(parent);
		} else if (fLexer.peekKeyword("final")) {
			parse_final(parent);
		} else if (id.equals("modport")) {
			modport_decl(parent);
		} else if (id.equals("assign")) {
			parse_continuous_assign(parent);
		} else if (id.equals("covergroup")) {
			parsers().covergroupParser().parse(parent);
		} else if (id.equals("constraint")) {
			fParsers.constraintParser().parse(parent, modifiers);
		} else if (id.equals("sequence")) {
			fParsers.sequenceParser().sequence(parent);
		} else if (id.equals("import")) {
			parsers().impExpParser().parse_import(parent);
		} else if (id.equals("clocking")) {
			fParsers.clockingBlockParser().parse(parent);
		} else if (id.equals("typedef")) {
			parsers().dataTypeParser().typedef(parent);
		} else if (id.equals("class")) {
			parsers().classParser().parse(parent, modifiers);
		} else if (id.equals("module") || id.equals("program") ||
				(id.equals("interface") && (modifiers & SVDBFieldItem.FieldAttr_Virtual) == 0)) {
			// enter module scope
			parsers().modIfcProgParser().parse(parent, modifiers);
		} else if (id.equals("parameter") || id.equals("localparam")) {
			parse_parameter_decl(parent);
		} else if (fLexer.peekKeyword("defparam")) {
			SVDBDefParamStmt defparam = new SVDBDefParamStmt();
			defparam.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
			
			parent.addChildItem(defparam);
			
			while (fLexer.peek() != null) {
				SVDBLocation is = fLexer.getStartLocation();
				SVDBDefParamItem item = new SVDBDefParamItem();
				item.setLocation(is);
				item.setTarget(fParsers.exprParser().hierarchical_identifier());
				fLexer.readOperator("=");
				item.setExpr(fParsers.exprParser().expression());
				
				defparam.addParamAssign(item);
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			fLexer.readOperator(";");
		} else if (SVDataTypeParser.NetType.contains(id)) {
			parse_var_decl(parent);
		} else if (fLexer.peekKeyword(SVKeywords.fBuiltinGates)) {
			parsers().gateInstanceParser().parse(parent);
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
		} else if (fLexer.peekKeyword("timeprecision","timeunit")) {
			parse_time_units_precision(parent);
		} else if (!fLexer.peekOperator()) {
			if (fLexer.peekId()) {
				SVToken tok = fLexer.consumeToken();
				if (fLexer.peekOperator(":")) {
					// Labeled assertion
					// TODO: preserve label
					fLexer.eatToken();
					parsers().assertionParser().parse(parent);
				} else {
					fLexer.ungetToken(tok);
					// likely a variable or module declaration
					debug("Likely VarDecl: " + id);
					parse_var_decl_module_inst(parent, modifiers);
				}
			} else {
				// likely a variable or module declaration
				debug("Likely VarDecl: " + id);
				parse_var_decl_module_inst(parent, modifiers);
			}
		} else {
			error("Unknown module/class/iterface body item: Operator " + fLexer.eatToken());
		}

		debug("<-- process_module_class_interface_body_item"); 
	}
	
	public void parse_parameter_decl(ISVDBAddChildItem parent) throws SVParseException {
		// local parameter
		fLexer.readKeyword("parameter", "localparam");
		
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
		
		parent.addChildItem(p);
		
		while (true) {
			pi = new SVDBVarDeclItem(param_name);
			
			if (fLexer.peekOperator("[")) {
				pi.setArrayDim(fParsers.dataTypeParser().var_dim());
			}
			if (fLexer.peekOperator("=")) {
				fLexer.eatToken();
				parsers().exprParser().expression();
			}
			
			pi.setLocation(it_start);
			p.addChildItem(pi);
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				it_start = fLexer.getStartLocation();
				param_name = fLexer.readId();
			} else {
				break;
			}
		}
		fLexer.readOperator(";");
	}
	
	public void parse_time_units_precision(ISVDBAddChildItem parent) throws SVParseException {
		String type = fLexer.readKeyword("timeprecision","timeunit");
		
		String num = fLexer.readNumber();
		
		if (type.equals("timeprecision")) {
			SVDBTimePrecisionStmt precision = new SVDBTimePrecisionStmt();
			precision.setArg1(num);
			if (fLexer.peekOperator("/")) {
				fLexer.eatToken();
				precision.setArg2(fLexer.readNumber());
			}
			parent.addChildItem(precision);
		} else {
			SVDBTimeUnitsStmt units = new SVDBTimeUnitsStmt();
			units.setUnits(num);
			parent.addChildItem(units);
		}
		
		fLexer.readOperator(";");
	}
	
	public void parse_continuous_assign(ISVDBAddChildItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("assign");
		SVDBAssign assign = new SVDBAssign();
		assign.setLocation(start);
		
		// [drive_strength] [delay3]

		// TODO: discarded for now
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			String s1=null, s2=null;
			if (fLexer.peekKeyword("highz1", "highz0")) {
				s1 = fLexer.eatToken();
				fLexer.readOperator(",");
				s2 = fLexer.readKeyword(SVKeywords.fStrength);
			} else {
				s1 = fLexer.readKeyword(SVKeywords.fStrength);
				fLexer.readOperator(",");
				if (fLexer.peekKeyword("highz1", "highz0")) {
					s2 = fLexer.eatToken();
				} else {
					s2 = fLexer.readKeyword(SVKeywords.fStrength);
				}
			}
			
			fLexer.readOperator(")");
		}

		if (fLexer.peekOperator("#")) {
			// Time expression
			assign.setDelay(fParsers.exprParser().delay_expr());
		}
		
		assign.setLHS(fParsers.exprParser().variable_lvalue());
		
		fLexer.readOperator("=");
		
		assign.setRHS(fParsers.exprParser().expression());
		
		fLexer.readOperator(";");
		
		parent.addChildItem(assign);
	}
	
	private void parse_var_decl(ISVDBAddChildItem parent) throws SVParseException {
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
		parent.addChildItem(var);
		while (true) {
			
			SVDBVarDeclItem vi = new SVDBVarDeclItem(net_name);
			vi.setLocation(start);
			var.addChildItem(vi);
			
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
	}
	
	public void parse_var_decl_module_inst(ISVDBAddChildItem parent, int modifiers) throws SVParseException {
		SVDBTypeInfo type;
		SVDBLocation start = fLexer.getStartLocation(), item_start;

		// TODO: need to modify this to be different for class and module/interface
		// scopes
		type = parsers().dataTypeParser().data_type(modifiers);
		
		item_start = fLexer.getStartLocation();
		String inst_name_or_var = fLexer.readIdOrKeyword();

		debug("inst name or var: " + inst_name_or_var);


		// SV allows modules to be arrayed
		// some_module module_instance_name [5:0] ( .a (a), .y (y));
		// so grab the dimentions here
		List<SVDBVarDimItem> arraydims = null;
		if (fLexer.peekOperator("[")) {
			// Array type
			arraydims = parsers().dataTypeParser().var_dim();
		}

		// Check to see if we have an '(' - we have a module at this point
		if (fLexer.peekOperator("(")) {
			// TODO: hopefully this is a user-defined type?
			debug("Module instance type: " + type.getClass().getName());
			type = new SVDBTypeInfoModuleIfc(type.getName());
			SVDBModIfcInst inst = new SVDBModIfcInst(type);
			inst.setLocation(start);
			
			parent.addChildItem(inst);

			while (fLexer.peek() != null) {
				// it's a module
				debug("module instantiation - " + inst_name_or_var);
				SVDBModIfcInstItem item = new SVDBModIfcInstItem(inst_name_or_var);
				if (arraydims != null) {
					item.setArrayDim(arraydims);
					arraydims = null;
				}
				item.setLocation(fLexer.getStartLocation());
				inst.addChildItem(item);
				
				SVDBParamValueAssignList port_map = fParsers.paramValueAssignParser().parse(false);
				item.setPortMap(port_map);

				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					start = fLexer.getStartLocation();
					inst_name_or_var = fLexer.readId();
					// Check to see if the instance is arrayed
					if (fLexer.peekOperator("[")) {
						arraydims = fParsers.dataTypeParser().var_dim();
					}
				} else {
					break;
				}
			}
			fLexer.readOperator(";");
		} 
		// non-module instance
		else {
			SVDBVarDeclStmt item = new SVDBVarDeclStmt(type, 0);
			item.setAttr(modifiers);
			item.setLocation(start);
			
			parent.addChildItem(item);

			while (fLexer.peek() != null) {
				SVDBVarDeclItem vi = new SVDBVarDeclItem(inst_name_or_var);
				vi.setLocation(item_start);

				// Set the array dimensions that we grabbed earlier in case there were any
				if (arraydims != null) {
					vi.setArrayDim(arraydims);
					arraydims = null;
				}

				item.addChildItem(vi);

				if (fLexer.peekOperator("=")) {
					fLexer.eatToken();
					vi.setInitExpr(fParsers.exprParser().expression());
				}

				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					start = fLexer.getStartLocation();
					inst_name_or_var = fLexer.readId();
					// Parse the next array dimension
					if (fLexer.peekOperator("[")) {
						arraydims = fParsers.dataTypeParser().var_dim();
					}
				} else {
					break;
				}
			}
			fLexer.readOperator(";");
		}
	}
	
	private void parse_final(ISVDBAddChildItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("final");
		
		SVDBBodyStmt ret = new SVDBFinalStmt();
		ret.setLocation(start);
		
		parent.addChildItem(ret);
		
		fParsers.behavioralBlockParser().statement(ret);
	}
	
	private void modport_decl(ISVDBAddChildItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("modport");
		SVDBModportDecl modport = new SVDBModportDecl();
		modport.setLocation(start);
		
		parent.addChildItem(modport);
		
		while (fLexer.peek() != null) {
			start = fLexer.getStartLocation();
			String id = fLexer.readId();
			SVDBModportItem item = new SVDBModportItem(id);
			item.setLocation(start);
			
			fLexer.readOperator("(");
			while (fLexer.peek() != null) {
				String type = fLexer.readKeyword("clocking","import","export",
						"input","output","inout");
				SVDBModportPortsDecl ports_decl = null;
				
				if (type.equals("clocking")) {
					ports_decl = modport_clocking_declaration();
					if (fLexer.peekOperator(",")) {
						fLexer.eatToken();
					}
				} else if (type.equals("import") || type.equals("export")) {
					ports_decl = modport_tf_ports_declaration(type);
				} else {
					ports_decl = modport_simple_ports_declaration(type);
				}
				
				item.addPorts(ports_decl);
				
				if (fLexer.peekOperator(")")) {
					break;
				}
			}
			fLexer.readOperator(")");

			modport.addModportItem(item);
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		fLexer.readOperator(";");
	}

	private SVDBModportClockingPortDecl modport_clocking_declaration() throws SVParseException {
		SVDBModportClockingPortDecl ret = new SVDBModportClockingPortDecl();
		ret.setClockingId(fLexer.readId());
		return ret;
	}
	
	private SVDBModportTFPortsDecl modport_tf_ports_declaration(String type) throws SVParseException {
		SVDBModportTFPortsDecl ret = new SVDBModportTFPortsDecl();
		ret.setImpExpType(type);
		
		while (fLexer.peek() != null) {
			SVDBModportTFPort port = new SVDBModportTFPort();
			port.setLocation(fLexer.getStartLocation());
			if (fLexer.peekKeyword("task","function")) {
				port.setPrototype(fParsers.taskFuncParser().parse_method_decl());
			} else {
				port.setId(fLexer.readId());
			}
			ret.addChildItem(port);
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
			
			// escape on next top-level element
			if (fLexer.peekKeyword()) {
				break;
			}
		}
		
		return ret;
	}
	
	private SVDBModportSimplePortsDecl modport_simple_ports_declaration(String dir) throws SVParseException {
		SVDBModportSimplePortsDecl ret = new SVDBModportSimplePortsDecl();
		ret.setPortDir(dir);
		
		while (fLexer.peek() != null) {
			SVDBModportSimplePort port = new SVDBModportSimplePort();
			port.setLocation(fLexer.getStartLocation());
			if (fLexer.peekOperator(".")) {
				port.setIsMapped(true);
				fLexer.eatToken();
			}
			port.setPortId(fLexer.readId());
			if (port.isMapped()) {
				fLexer.readOperator("(");
				port.setExpr(fParsers.exprParser().expression());
				fLexer.readOperator(")");
			}
			ret.addPort(port);
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
			
			if (fLexer.peekKeyword()) {
				break;
			}
		}
		
		return ret;
	}
	
	private void parse_initial_always(ISVDBAddChildItem parent) throws SVParseException {
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
			SVDBAlwaysStmt always_stmt = new SVDBAlwaysStmt(always_type);
			
			// TODO: Store always types in SVDBItem 
			// Can have the following formats:
			// @*
			// @(*)
			// @ expression
			// @ (expression)
			if (lexer().peekOperator("@")) {
				lexer().eatToken();
				// Just kill the open brace
				if (lexer().peekOperator("("))  {
					lexer().readOperator("(");
				}
				// Check for @*
				if (lexer().peekOperator("*")) {
					lexer().eatToken();
					always_stmt.setAlwaysEventType(AlwaysEventType.Any);
				}
				// Suck in the expression itself
				else {
					always_stmt.setEventExpr(fParsers.exprParser().event_expression());
					always_stmt.setAlwaysEventType(AlwaysEventType.Expr);
				}
				// blindly eat the closing brace if it exists
				if (lexer().peekOperator(")"))  {
					lexer().readOperator(")");
				}
			} else {
				always_stmt.setAlwaysEventType(AlwaysEventType.None);
			}
			ret = always_stmt;
		} else {
			ret = new SVDBInitialStmt();
		}
		ret.setLocation(start);
		
		parent.addChildItem(ret);
		fParsers.behavioralBlockParser().statement((SVDBBodyStmt)ret);
	}
}

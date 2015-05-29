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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBAlias;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBAssignItem;
import net.sf.sveditor.core.db.SVDBBind;
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
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr.ClockingEventType;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
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
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		int modifiers = 0;
		if (fLexer.peekOperator(OP.LPAREN_MUL)) {
			fParsers.attrParser().parse(parent);
		}
		String id = fLexer.peek();

		if (fDebugEn) {
			debug("--> process_module_class_interface_body_item: \"" + id + 
					"\" @ " + SVDBLocation.unpackLineno(fLexer.getStartLocation()));
		}

		// Save the start location before qualifiers
		long start = fLexer.getStartLocation();
		modifiers = fParsers.SVParser().scan_qualifiers(false);
		
//		id = fLexer.peek();
		KW kw = fLexer.peekKeywordE();

		if (kw != null) {

			if (fDebugEn) {
				debug("body item kw is: " + kw);
			}
			
			switch (kw) {
				case ALIAS:
					parse_alias(parent, start);
					break;
			
				case FUNCTION:
				case TASK:
					parsers().taskFuncParser().parse(parent, start, modifiers);
					break;
					
				case ASSERT:
				case ASSUME:
				case COVER:
				case RESTRICT:
				case EXPECT:
					parsers().assertionParser().parse(parent, "");
					break;
					
				case PROPERTY:
					fParsers.propertyParser().property(parent);
					break;
					
				case GENERATE:
				case FOR:
				case IF:
				case CASE:
					// Generate-block statements
					parsers().generateBlockParser().parse(parent);
					break;
					
				case SPECIFY:
					parsers().specifyBlockParser().parse(parent);
					break;
					
				case DEFAULT:
				case GLOBAL:
				case CLOCKING:
					// Clocking block
					parsers().clockingBlockParser().parse(parent);
					break;
					
				case ALWAYS:
				case ALWAYS_COMB:
				case ALWAYS_LATCH:
				case ALWAYS_FF:
				case INITIAL:
					parse_initial_always(parent);
					break;
					
				case FINAL:
					parse_final(parent);
					break;
					
				case MODPORT:
					modport_decl(parent);
					break;
					
				case ASSIGN:
					parse_continuous_assign(parent);
					break;
					
				case BIND:
					parse_bind(parent);
					break;
					
				case COVERGROUP:
					fParsers.covergroupParser().parse(parent);
					break;
					
				case CONSTRAINT:
					fParsers.constraintParser().parse(parent, modifiers);
					break;
					
				case SEQUENCE:
					fParsers.sequenceParser().sequence(parent);
					break;
					
				case IMPORT:
					fParsers.impExpParser().parse_import(parent);
					break;
					
				case EXPORT:
					fParsers.impExpParser().parse_export(parent);
					break;
					
				case TYPEDEF:
					fParsers.dataTypeParser().typedef(parent);
					break;
					
				case CLASS:
					parsers().classParser().parse(parent, modifiers);
					break;
					
				case MODULE:
				case PROGRAM:
				case INTERFACE:
					if (kw == KW.INTERFACE) {
						if ((modifiers & SVDBFieldItem.FieldAttr_Virtual) == 0) {
							parsers().modIfcProgParser().parse(parent, modifiers);
						} else {
							parse_var_decl_module_inst(parent, modifiers);
						}
					} else {
						parsers().modIfcProgParser().parse(parent, modifiers);
					}
					break;
					
				case PARAMETER:
				case LOCALPARAM:
					parse_parameter_decl(parent);
					break;
					
				case DEFPARAM: 
				case SPECPARAM: {
					SVDBDefParamStmt defparam = new SVDBDefParamStmt();
					defparam.setLocation(fLexer.getStartLocation());
					fLexer.eatToken();

					parent.addChildItem(defparam);

					while (fLexer.peek() != null) {
						long is = fLexer.getStartLocation();
						SVDBDefParamItem item = new SVDBDefParamItem();
						item.setLocation(is);
						item.setTarget(fParsers.exprParser().hierarchical_identifier());
						fLexer.readOperator(OP.EQ);
						item.setExpr(fParsers.exprParser().expression());

						defparam.addParamAssign(item);

						if (fLexer.peekOperator(OP.COMMA)) {
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator(OP.SEMICOLON);
					} break;
				
				case TIMEPRECISION:
				case TIMEUNIT:
					parse_time_units_precision(parent);
					break;
					
				case CMOS:
				case RCMOS:
				case BUFIF0:
				case BUFIF1:
				case NOTIF0:
				case NOTIF1:
				case NMOS:
				case PMOS:
				case RNMOS:
				case RPMOS:
				case AND:
				case NAND:
				case OR:
				case NOR:
				case XOR:
				case XNOR:
				case BUF:
				case NOT:
				case PULLUP:
				case PULLDOWN:
				case TRANIF0:
				case TRANIF1:
				case RTRANIF1:
				case RTRANIF0:
				case TRAN:
				case RTRAN:
					parsers().gateInstanceParser().parse(parent);
					break;
					
				default:
					if (SVDataTypeParser.NetTypeE.contains(kw)) {
						parse_var_decl_net_type (parent);
					} else {
						parse_var_decl_module_inst(parent, modifiers);
//						error("unknown ModIfcBodyItem: " + kw);
					}
			}
		} else { // kw null
			
			if (fLexer.peekOperator(OP.SEMICOLON)) {
				// null statement
				SVDBNullStmt stmt = new SVDBNullStmt();
				stmt.setLocation(fLexer.getStartLocation());
				fLexer.eatToken();
				parent.addChildItem(stmt);
			} else if (!fLexer.peekOperator()) {
				if (fLexer.peekId()) {
					SVToken tok = fLexer.consumeToken();
					if (fLexer.peekOperator(OP.COLON)) {
						// Labeled assertion
						String assertion_label = tok.getImage();
						fLexer.eatToken();
						parsers().assertionParser().parse(parent, assertion_label);
					} else {
						fLexer.ungetToken(tok);
						// likely a variable or module declaration
						if (fDebugEn) {
							debug("Likely VarDecl: " + id);
						}
						parse_var_decl_module_inst(parent, modifiers);
					}
				} else {
					// likely a variable or module declaration
					if (fDebugEn) {
						debug("Likely VarDecl: " + id);
					}
					parse_var_decl_module_inst(parent, modifiers);
				}
			} else {
				error("Unknown module/class/iterface body item: Operator " + fLexer.eatTokenR());
			}
		}
					
//		} else if (id.equals("module") || id.equals("program") ||
//				(id.equals("interface") && (modifiers & SVDBFieldItem.FieldAttr_Virtual) == 0)) {
//			// enter module scope
//			parsers().modIfcProgParser().parse(parent, modifiers);


		if (fDebugEn) {
			debug("<-- process_module_class_interface_body_item");
		}
	}
	
	public void parse_parameter_decl(ISVDBAddChildItem parent) throws SVParseException {
		long param_start = fLexer.getStartLocation();
		// local parameter
		fLexer.readKeyword(KW.PARAMETER, KW.LOCALPARAM);
		
		if (fLexer.peekKeyword(KW.TYPE)) {
			fLexer.eatToken();
		}
		SVDBTypeInfo data_type = parsers().dataTypeParser().data_type(0);
		String param_name;
		
		long it_start = fLexer.getStartLocation();
		
		if (fLexer.peekId()) {
			// likely a typed parameter
			param_name = fLexer.readId();
		} else {
			// likely an untyped parameter
			param_name = data_type.getName();
			data_type = null;
		}
		
		SVDBParamPortDecl p = new SVDBParamPortDecl(data_type);
		p.setLocation(param_start);
		SVDBVarDeclItem pi;
		
		parent.addChildItem(p);
		
		while (true) {
			pi = new SVDBVarDeclItem(param_name);
			
			if (fLexer.peekOperator(OP.LBRACKET)) {
				pi.setArrayDim(fParsers.dataTypeParser().var_dim());
			}
			if (fLexer.peekOperator(OP.EQ)) {
				fLexer.eatToken();
				parsers().exprParser().expression();
			}
			
			pi.setLocation(it_start);
			p.addChildItem(pi);
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
				it_start = fLexer.getStartLocation();
				param_name = fLexer.readId();
			} else {
				break;
			}
		}
		fLexer.readOperator(OP.SEMICOLON);
	}
	
	public void parse_time_units_precision(ISVDBAddChildItem parent) throws SVParseException {
		KW type = fLexer.readKeyword(KW.TIMEPRECISION, KW.TIMEUNIT);
		
		String num = fLexer.readNumber();
		
		if (type == KW.TIMEPRECISION) {
			SVDBTimePrecisionStmt precision = new SVDBTimePrecisionStmt();
			precision.setArg1(num);
			if (fLexer.peekOperator(OP.DIV)) {
				fLexer.eatToken();
				precision.setArg2(fLexer.readNumber());
			}
			parent.addChildItem(precision);
		} else {
			SVDBTimeUnitsStmt units = new SVDBTimeUnitsStmt();
			units.setUnits(num);
			parent.addChildItem(units);
		}
		
		fLexer.readOperator(OP.SEMICOLON);
	}
	
	public void parse_continuous_assign(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		fLexer.readKeyword(KW.ASSIGN);
		SVDBAssign assign = new SVDBAssign();
		assign.setLocation(start);
		
		// [drive_strength] [delay3]

		// TODO: discarded for now
		if (fLexer.peekOperator(OP.LPAREN)) {
			fLexer.eatToken();
			String s1=null, s2=null;
			if (fLexer.peekKeyword(KW.HIGHZ1, KW.HIGHZ0)) {
				s1 = fLexer.eatTokenR();
				fLexer.readOperator(OP.COMMA);
				s2 = fLexer.readKeyword(SVKeywords.fStrength).getImg();
			} else {
				s1 = fLexer.readKeyword(SVKeywords.fStrength).getImg();
				fLexer.readOperator(OP.COMMA);
				if (fLexer.peekKeyword(KW.HIGHZ1, KW.HIGHZ0)) {
					s2 = fLexer.eatTokenR();
				} else {
					s2 = fLexer.readKeyword(SVKeywords.fStrength).getImg();
				}
			}
			
			fLexer.readOperator(OP.RPAREN);
		}

		if (fLexer.peekOperator(OP.HASH)) {
			// Time expression
			assign.setDelay(fParsers.exprParser().delay_expr(3));
		}
		
		while (fLexer.peek() != null) {
			SVDBAssignItem item = new SVDBAssignItem();
			item.setLocation(fLexer.getStartLocation());
			item.setLHS(fParsers.exprParser().variable_lvalue());
			
			fLexer.readOperator(OP.EQ);
			
			item.setRHS(fParsers.exprParser().expression());
			
			assign.addChildItem(item);
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		
		parent.addChildItem(assign);
	}
	
	/**
	 * This function is used to parse two different types of data lines.  Net types, and
	 * port lists.
	 * Net Type Declaration:
	 *	net_declaration ::= 
	 *  net_type [ drive_strength | charge_strength ] [  vectored  |  scalared  ] 
	 *  data_type_or_implicit [ delay3 ] list_of_net_decl_assignments ;
	 * @param parent
	 * @throws SVParseException
	 * 
	 * Port list declaration:
	 * [input|output|inout] [net_type] ... list_of_net_decl_assignments;
	 * Supply1 supply0 
	 */
	private void parse_var_decl_net_type (ISVDBAddChildItem parent) throws SVParseException {
		// net type
		String net_type = fLexer.eatTokenR();		// at this point net_type can be an invalid net type, such as a direction - input, output or inout
		String vector_dim = null;
		SVDBVarDeclStmt var = null;
		String net_name = null;
		long start = -1;
		SVDBTypeInfoBuiltinNet type_info = null;
		SVDBTypeInfo data_type = null;
		
		if (fDebugEn) {
			debug("Net Type: " + net_type + " @ " + 
					SVDBLocation.unpackLineno(fLexer.getStartLocation()));
		}
		
		// Drive Strength
		if (fLexer.peekOperator(OP.LPAREN))  {
			SVToken tok = new SVToken ();
			tok = fLexer.consumeToken();		// eat the (
			if (fLexer.peekKeyword(SVKeywords.fStrength))  {
				// Have (<strength>, <strength>)
				KW strength1 = fLexer.readKeyword(SVKeywords.fStrength);
				fLexer.readOperator(OP.COMMA);		// 
				KW strength2 = fLexer.readKeyword(SVKeywords.fStrength);
				fLexer.readOperator(OP.RPAREN);		//
				// TODO: Do something with the strengths
			}
			else  {
				fLexer.ungetToken(tok);// restore the (
			}
		}

		// Delay 3
		// #(mintypmax,mintypmax, mintypmax)
		if (fLexer.peekOperator(OP.HASH))  {
			// Time expression
			fParsers.exprParser().delay_expr(3);
			// TODO - What Do something with the Delay expression
		}

		// vectored untyped net
		if (fLexer.peekOperator(OP.LBRACKET)) {
			// TODO:
			data_type = new SVDBTypeInfoBuiltin(net_type);
			((SVDBTypeInfoBuiltin)data_type).setVectorDim(
					fParsers.dataTypeParser().vector_dim());
		}
		else  {
			// At this point set the data type to a generic, untyped data type.
			data_type = parsers().dataTypeParser().data_type(0);
		}
		
		// Delay 3
		// #(mintypmax,mintypmax, mintypmax)
		if (fLexer.peekOperator(OP.HASH))  {
			// Time expression
			fParsers.exprParser().delay_expr(3);
			// TODO - What Do something with the Delay expression
		}

		// Now, based on what we see next, we determine whether the
		// net is typed or untyped
		if (fLexer.peekOperator(OP.COMMA, OP.SEMICOLON, OP.EQ)) {
			// The net was untyped
			net_name = data_type.getName();
			data_type = new SVDBTypeInfoBuiltin(net_type);
		} else {
			// Assume the net to be typed
			net_name = fLexer.readId();
		}
		start = fLexer.getStartLocation();
		type_info = new SVDBTypeInfoBuiltinNet(net_type, data_type);
		
		var = new SVDBVarDeclStmt(type_info, 0);
		parent.addChildItem(var);
		while (true) {
			
			SVDBVarDeclItem vi = new SVDBVarDeclItem(net_name);
			vi.setLocation(start);
			var.addChildItem(vi);
			
			if (fLexer.peekOperator(OP.LBRACKET)) {
				vi.setArrayDim(parsers().dataTypeParser().var_dim());
			}
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
				start = fLexer.getStartLocation();
				net_name = fLexer.readId();
			} else if (fLexer.peekOperator(OP.EQ)) {
				// Initialized wire
				fLexer.eatToken();
				parsers().exprParser().expression();
			} else {
				break;
			}
		}
		
		fLexer.readOperator(OP.SEMICOLON);
	}
	
	public void parse_bind(ISVDBAddChildItem parent) throws SVParseException {
		SVDBBind bind = new SVDBBind();
		bind.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword(KW.BIND);
		
		bind.setTargetTypeName(fParsers.exprParser().variable_lvalue());
		
		parent.addChildItem(bind);
		
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			// Have a list of instance names
			while (fLexer.peek() != null) {
				bind.addTargetInstName(fParsers.exprParser().hierarchical_identifier());
				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		}

		// Parse the module instantiation
		// Note: module instantiation includes the trailing ';'
		fParsers.modIfcBodyItemParser().parse_var_decl_module_inst(bind, 0);
	}
	
	public void parse_var_decl_module_inst(ISVDBAddChildItem parent, int modifiers) throws SVParseException {
		SVDBTypeInfo type;
		long start = fLexer.getStartLocation(), item_start;

		// TODO: need to modify this to be different for class and module/interface
		// scopes
		type = parsers().dataTypeParser().data_type(modifiers);
		
		item_start = fLexer.getStartLocation();
		String inst_name_or_var = fLexer.readIdOrKeyword();

		if (fDebugEn) {
			debug("inst name or var: " + inst_name_or_var);
		}


		// SV allows modules to be arrayed
		// some_module module_instance_name [5:0] ( .a (a), .y (y));
		// so grab the dimensions here
		List<SVDBVarDimItem> arraydims = null;
		if (fLexer.peekOperator(OP.LBRACKET)) {
			// Array type
			arraydims = parsers().dataTypeParser().var_dim();
		}

		// Check to see if we have an '(' - we have a module at this point
		if (fLexer.peekOperator(OP.LPAREN)) {
			// TODO: hopefully this is a user-defined type?
			if (fDebugEn) {
				debug("Module instance type: " + type.getClass().getName());
			}
			type = new SVDBTypeInfoModuleIfc(type.getName());
			SVDBModIfcInst inst = new SVDBModIfcInst(type);
			inst.setLocation(start);
			
			parent.addChildItem(inst);

			while (fLexer.peek() != null) {
				// it's a module
				if (fDebugEn) {
					debug("module instantiation - " + inst_name_or_var);
				}
				SVDBModIfcInstItem item = new SVDBModIfcInstItem(inst_name_or_var);
				if (arraydims != null) {
					item.setArrayDim(arraydims);
					arraydims = null;
				}
				item.setLocation(fLexer.getStartLocation());
				inst.addChildItem(item);
				
				SVDBParamValueAssignList port_map = fParsers.paramValueAssignParser().parse(false);
				item.setPortMap(port_map);

				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
					start = fLexer.getStartLocation();
					inst_name_or_var = fLexer.readId();
					// Check to see if the instance is arrayed
					if (fLexer.peekOperator(OP.LBRACKET)) {
						arraydims = fParsers.dataTypeParser().var_dim();
					}
				} else {
					break;
				}
			}
			fLexer.readOperator(OP.SEMICOLON);
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

				if (fLexer.peekOperator(OP.EQ)) {
					fLexer.eatToken();
					vi.setInitExpr(fParsers.exprParser().expression());
				}

				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
					start = fLexer.getStartLocation();
					inst_name_or_var = fLexer.readId();
					// Parse the next array dimension
					if (fLexer.peekOperator(OP.LBRACKET)) {
						arraydims = fParsers.dataTypeParser().var_dim();
					}
				} else {
					break;
				}
			}
			fLexer.readOperator(OP.SEMICOLON);
		}
	}
	
	private void parse_final(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		fLexer.readKeyword(KW.FINAL);
		
		SVDBBodyStmt ret = new SVDBFinalStmt();
		ret.setLocation(start);
		
		parent.addChildItem(ret);
		
		fParsers.behavioralBlockParser().statement(ret);
	}
	
	private void modport_decl(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		fLexer.readKeyword(KW.MODPORT);
		SVDBModportDecl modport = new SVDBModportDecl();
		modport.setLocation(start);
		
		parent.addChildItem(modport);
		
		while (fLexer.peek() != null) {
			start = fLexer.getStartLocation();
			String id = fLexer.readId();
			SVDBModportItem item = new SVDBModportItem(id);
			item.setLocation(start);
			
			fLexer.readOperator(OP.LPAREN);
			while (fLexer.peek() != null) {
				KW type = fLexer.readKeyword(KW.CLOCKING, KW.IMPORT, KW.EXPORT, KW.INPUT, KW.OUTPUT, KW.INOUT);
				SVDBModportPortsDecl ports_decl = null;
				
				if (type.equals("clocking")) {
					ports_decl = modport_clocking_declaration();
					if (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
					}
				} else if (type == KW.IMPORT || type == KW.EXPORT) {
					ports_decl = modport_tf_ports_declaration(type.getImg());
				} else {
					ports_decl = modport_simple_ports_declaration(type.getImg());
				}
				
				item.addPorts(ports_decl);
				
				if (fLexer.peekOperator(OP.RPAREN)) {
					break;
				}
			}
			fLexer.readOperator(OP.RPAREN);

			modport.addModportItem(item);
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		fLexer.readOperator(OP.SEMICOLON);
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
			if (fLexer.peekKeyword(KW.TASK, KW.FUNCTION)) {
				port.setPrototype(fParsers.taskFuncParser().parse_method_decl());
			} else {
				port.setId(fLexer.readId());
			}
			ret.addChildItem(port);
			
			if (fLexer.peekOperator(OP.COMMA)) {
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
		if (fDebugEn) {
			debug("--> modport_simple_ports_declaration: " + dir);
		}
		ret.setPortDir(dir);
		
		while (fLexer.peek() != null) {
			SVDBModportSimplePort port = new SVDBModportSimplePort();
			port.setLocation(fLexer.getStartLocation());
			if (fLexer.peekOperator(OP.DOT)) {
				port.setIsMapped(true);
				fLexer.eatToken();
			}
			port.setPortId(fLexer.readId());
			if (port.isMapped()) {
				fLexer.readOperator(OP.LPAREN);
				port.setExpr(fParsers.exprParser().expression());
				fLexer.readOperator(OP.RPAREN);
			}
			if (fDebugEn) {
				debug(" -- Add port " + port.getPortId());
			}
			ret.addPort(port);
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
			
			if (fLexer.peekKeyword()) {
				break;
			}
		}
		
		if (fDebugEn) {
			debug("<-- modport_simple_ports_declaration: " + dir);
		}
		
		return ret;
	}
	
	private static final Set<KW> initial_always_kw;
	static {
		initial_always_kw = new HashSet<ISVKeywords.KW>();
		initial_always_kw.add(KW.INITIAL);
		initial_always_kw.add(KW.ALWAYS);
		initial_always_kw.add(KW.ALWAYS_COMB);
		initial_always_kw.add(KW.ALWAYS_LATCH);
		initial_always_kw.add(KW.ALWAYS_FF);
	}
	
	private void parse_alias(ISVDBAddChildItem parent, long start) throws SVParseException {
		fLexer.readKeyword(KW.ALIAS);
		
		SVDBAlias alias = new SVDBAlias();
		alias.setLocation(start);
		
		alias.setLvalue(fParsers.exprParser().variable_lvalue());
		
		while (true) {
			fLexer.readOperator(OP.EQ);
			
			alias.addAlias(fParsers.exprParser().variable_lvalue());
		
			if (!fLexer.peekOperator(OP.EQ)) {
				break;
			}
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		
		parent.addChildItem(alias);
	}
	
	private void parse_initial_always(ISVDBAddChildItem parent) throws SVParseException {
		ISVDBChildItem ret = null;
		long start = fLexer.getStartLocation();
		KW type = fLexer.readKeyword(initial_always_kw);

		if (type != KW.INITIAL) { // always
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
			if ((always_type == AlwaysType.AlwaysFF) || (always_type == AlwaysType.Always))  {
				
				// TODO: Store always types in SVDBItem 
				// Can have the following formats:
				// @*
				// @(*)
				// @ expression
				// @ (expression)
				if (lexer().peekOperator(OP.AT)) {
					always_stmt.setCBEventExpr(parsers().exprParser().clocking_event());
				} else {
					always_stmt.setAlwaysEventType(ClockingEventType.None);
				}
			// Remaining always types don't have clocking blocks
			} else {
				always_stmt.setAlwaysEventType(ClockingEventType.None);
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

/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import sun.awt.FwDispatcher;
import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoClassItem;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.SVDBTypeInfoFwdDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;
import net.sf.sveditor.core.db.SVDBTypeInfoUnion;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeExpr;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem.DimType;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVDataTypeParser extends SVParserBase {
//	public static final Set<String>			IntegerAtomType;
//	public static final Set<String>			IntegerVectorType;
//	public static final Set<String>			IntegerTypes;
//	public static final Set<String>			NonIntegerType;
	public static final Set<KW>				NetTypeE;
	public static final Set<String>			BuiltInTypes;
	
	static {
//		IntegerAtomType = new HashSet<String>();
//		IntegerAtomType.add("byte");
//		IntegerAtomType.add("shortint");
//		IntegerAtomType.add("int");
//		IntegerAtomType.add("longint");
//		IntegerAtomType.add("integer");
//		IntegerAtomType.add("time");
//		IntegerAtomType.add("genvar"); // Treat genvar as an integer
//		IntegerVectorType = new HashSet<String>();
//		IntegerVectorType.add("bit");
//		IntegerVectorType.add("logic");
//		IntegerVectorType.add("reg");
//		IntegerTypes = new HashSet<String>();
//		IntegerTypes.addAll(IntegerAtomType);
//		IntegerTypes.addAll(IntegerVectorType);
		
//		NonIntegerType = new HashSet<String>();
//		NonIntegerType.add("shortreal");
//		NonIntegerType.add("real");
//		NonIntegerType.add("realtime");
		
		NetTypeE = new HashSet<KW>();
		NetTypeE.add(KW.SUPPLY0);
		NetTypeE.add(KW.SUPPLY1);
		NetTypeE.add(KW.TRI);
		NetTypeE.add(KW.TRIAND);
		NetTypeE.add(KW.TRIOR);
		NetTypeE.add(KW.TRIREG);
		NetTypeE.add(KW.TRI0);
		NetTypeE.add(KW.TRI1);
		NetTypeE.add(KW.UWIRE);
		NetTypeE.add(KW.WIRE);
		NetTypeE.add(KW.WAND);
		NetTypeE.add(KW.WOR);
		NetTypeE.add(KW.INPUT);
		NetTypeE.add(KW.OUTPUT);
		NetTypeE.add(KW.INOUT);
		
		BuiltInTypes = new HashSet<String>();
		BuiltInTypes.add("string");
		BuiltInTypes.add("chandle");
		BuiltInTypes.add("event");
	}
	
	public SVDataTypeParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBTypeInfo data_type(int qualifiers) throws SVParseException {
		SVDBTypeInfo type = null;
		SVToken tok;
		
		if (fDebugEn) {
			debug("--> data_type " + fLexer.peek());
		}

		qualifiers |= parsers().SVParser().scan_qualifiers(false);
		tok = fLexer.consumeToken();
		fLexer.ungetToken(tok);
		
		KW kw = fLexer.peekKeywordE();
		
		if (kw != null) {
			switch (kw) {
			
				// integer_vector_type [signing] { packed_dimension }
				case BIT:
				case LOGIC:
				case REG: {
					SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(fLexer.eatTokenR());
			
					// signing
					if (fLexer.peekKeyword(KW.SIGNED, KW.UNSIGNED)) {
						builtin_type.setAttr(fLexer.peekKeyword(KW.SIGNED)?
								SVDBTypeInfoBuiltin.TypeAttr_Signed:
									SVDBTypeInfoBuiltin.TypeAttr_Unsigned);
						fLexer.eatToken();
					}
			
					while (fLexer.peekOperator(OP.LBRACKET)) {
						if (fDebugEn) {
							debug("  IntegerVectorType vector");
						}
						builtin_type.setArrayDim(vector_dim());
					}
					type = builtin_type;
					} break;
				case SUPPLY0:
				case SUPPLY1:
				case TRI:
				case TRIAND:
				case TRIOR:
				case TRIREG:
				case TRI0:
				case TRI1:
				case UWIRE:
				case WIRE:
				case WAND:
				case WOR:
				case INPUT:
				case OUTPUT:
				case INOUT: {
					//	net_declaration
					//	13
					//	 ::= 
					//	net_type [ drive_strength | charge_strength ] [  vectored  |  scalared  ] 
					//	data_type_or_implicit [ delay3 ] list_of_net_decl_assignments ;  
					debug("NetType");
					SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(fLexer.eatTokenR());

					// Drive Strength
					if (fLexer.peekOperator(OP.LPAREN))  {
						tok = fLexer.consumeToken();		// eat the (
						if (fLexer.peekKeyword(SVKeywords.fStrength))  {
							// Have (<strength>, <strength>)
							KW strength1 = fLexer.readKeyword(SVKeywords.fStrength);
							fLexer.readOperator(OP.COMMA);		// 
							KW strength2 = fLexer.readKeyword(SVKeywords.fStrength);
							fLexer.readOperator(OP.RPAREN);		//
							// TODO: Do something with the strengths
						} else {
							fLexer.ungetToken(tok);// restore the (
						}
					}
					// Array dimensions
					if (fLexer.peekOperator(OP.LBRACKET)) {
						if (fDebugEn) {
							debug("  vector type");
						}
						builtin_type.setVectorDim(vector_dim());
					}
					// Delay 3
					// #(mintypmax,mintypmax, mintypmax)
					if (fLexer.peekOperator(OP.HASH))  {
						// Time expression
						fParsers.exprParser().delay_expr(3);
						// TODO - What Do something with the Delay expression
					}
					type = builtin_type;
					} break;
					
				case BYTE:
				case SHORTINT:
				case INT:
				case LONGINT:
				case INTEGER:
				case TIME:
				case GENVAR: {
					SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(fLexer.eatTokenR());

					if (fLexer.peekKeyword(KW.SIGNED, KW.UNSIGNED)) {
						builtin_type.setAttr(fLexer.peekKeyword(KW.SIGNED)?
								SVDBTypeInfoBuiltin.TypeAttr_Signed:
									SVDBTypeInfoBuiltin.TypeAttr_Unsigned);
						fLexer.eatToken();
					}
					type = builtin_type;
					} break;
					
				case SHORTREAL:
				case REAL:
				case REALTIME: {
					type = new SVDBTypeInfoBuiltin(fLexer.eatTokenR());
					} break;
					
				case STRUCT:
				case UNION: {
					//					tok = fLexer.readKeywordTok(KW.STRUCT, KW.UNION);
					tok = fLexer.consumeToken();
					if (tok.getImage().equals("union")) {
						// TODO: preserve?
						if (fLexer.peekKeyword(KW.TAGGED)) {
							fLexer.eatToken();
						}
					}

					if (fLexer.peekKeyword(KW.PACKED)) {
						// TODO: preserve?
						fLexer.eatToken(); 
					}

					if (fLexer.peekKeyword(KW.SIGNED, KW.UNSIGNED)) {
						// TODO: preserve?
						fLexer.eatToken();
					}

					type = (tok.getImage().equals("union"))?new SVDBTypeInfoUnion():new SVDBTypeInfoStruct();
					struct_union_body((ISVDBAddChildItem)type);
					} break;
					
				case ENUM: {
					type = enum_type();
					type.setName("<<ANONYMOUS>>");
					} break;
					
				case STRING:
				case CHANDLE:
				case EVENT:
					// string, chandle, etc
					type = new SVDBTypeInfoBuiltin(fLexer.eatTokenR());
					break;
					
				case VIRTUAL:
					// } else if (fLexer.peekKeyword("virtual") || (qualifiers & SVDBFieldItem.FieldAttr_Virtual) != 0) {
					type = virtual_type();
					break;
					
				case TYPE: {
					// type_reference ::=
					//   type ( expression )
					//   type ( data_type )
					type = new SVDBTypeInfoBuiltin(fLexer.eatTokenR());
					// TODO: skip paren expression
					error("'type' expression unsupported");
					} break;
					
			// Class type
				case CLASS: {
					type = class_fwd_type();
					} break;
					
				case SIGNED:
				case UNSIGNED: {
					// TODO: also applies if the operator is '['
					type = implicit_type();
				} break;
				
				case INTERFACE:
					type = virtual_type();
					break;
//		} else if (fLexer.peekOperator(OP.LBRACKET) || fLexer.peekKeyword("signed", "unsigned")) {
				
				default:
//					if (SVKeywords.isVKeyword(fLexer.peek()) && 
//							!fLexer.peekKeyword("interface") && 
//							!fLexer.peekKeyword(SVKeywords.fBuiltinGates)) {
						// ERROR: 
					error("Invalid type name \"" + fLexer.peek() + "\"");
					break;
			}
		} else if (fLexer.peekOperator(OP.LBRACKET)) {
			type = implicit_type();
		} else {
			String id = fLexer.eatTokenR();
			SVDBParamValueAssignList p_list = null;
			
			// Parameterized type?
			if (fLexer.peekOperator(OP.HASH)) {
				fLexer.eatToken();
				// Read in parameter list
				p_list = parsers().paramValueAssignParser().parse(false);
			}
			
			// Should be a user-defined type
			if (fLexer.peekOperator(OP.COLON2)) {
				StringBuilder type_id = new StringBuilder();
				type_id.append(id);
				
				// scoped type
				// [class_scope | package_scope] type_identifier { packed_dimension }
				while (fLexer.peekOperator(OP.COLON2)) {
					SVToken colon_tok = fLexer.consumeToken();
					SVToken id_tok = fLexer.consumeToken();
					if (fLexer.peekOperator(OP.LPAREN)) {
						// This sure looks like a function call
						fLexer.ungetToken(id_tok);
						fLexer.ungetToken(colon_tok);
						break;
					} else {
						type_id.append(colon_tok.getImage());
						type_id.append(id_tok.getImage());
					}
				}
				
				type = new SVDBTypeInfoUserDef(type_id.toString());
				
				if (fLexer.peekOperator(OP.LBRACKET)) {
					// TODO: packed_dimension
					type.setArrayDim(packed_dim());
				}
			} else if (fLexer.peekOperator(OP.DOT)) {
				// Interface type: interface.modport
				StringBuilder type_id = new StringBuilder();
				type_id.append(id);
				
				while (fLexer.peekOperator(OP.DOT)) {
					type_id.append(fLexer.eatTokenR()); // .
					type_id.append(fLexer.readId());
				}
				
				type = new SVDBTypeInfoUserDef(type_id.toString());
			} else {
				type = new SVDBTypeInfoUserDef(id);
			}
			
			((SVDBTypeInfoUserDef)type).setParameters(p_list);
			
			if (fLexer.peekOperator(OP.HASH)) {
				SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse(true);
				((SVDBTypeInfoUserDef)type).setParameters(plist);
			}
			
			// A sized enum is allowed to have a duplicate bit-width assigned
			if (fLexer.peekOperator(OP.LBRACKET)) {
				// TODO: this is a bit lax, since var_dim allows '$', '*', '<type>' array dimension
				if (fDebugEn) {
					debug("  sized enum type");
				}
				type.setArrayDim(var_dim());
			}
		}
		
		if (type == null) {
			error("Unknown type starting with \"" + fLexer.peek() + "\"");
		}
		
		if (fDebugEn) {
			debug("<-- data_type " + fLexer.peek());
		}
		
		return type;
	}
		
	private SVDBTypeInfo implicit_type() throws SVParseException {
		// Implicit items
		SVToken id = fLexer.consumeToken();
		SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(
				(id.getImage().equals("["))?"bit":id.getImage());
		
		// Implicit sized item
		
		debug("implicit type - " + id.getImage());

		if (id.getImage().equals("[")) {
			fLexer.ungetToken(id);
			builtin_type.setVectorDim(vector_dim());
		} else if (fLexer.peekOperator(OP.LBRACKET)) {
			builtin_type.setVectorDim(vector_dim());
		}
		
		return builtin_type;		
	}
		
	private SVDBTypeInfo virtual_type() throws SVParseException {
		SVToken tok;

		if (fLexer.peekKeyword(KW.VIRTUAL)) {
			fLexer.eatToken();
		}
		// virtual [interface] interface_identifier
		if (fLexer.peekKeyword(KW.INTERFACE)) {
			// TODO: use this somehow (?)
			fLexer.eatToken();
		}
		tok = fLexer.readIdTok();
		SVDBTypeInfoUserDef ud_type = new SVDBTypeInfoUserDef(tok.getImage());
		if (fLexer.peekOperator(OP.HASH)) {
			SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse(true);
			ud_type.setParameters(plist);
		}
		
		// May be referring to the modport
		if (fLexer.peekOperator(OP.DOT)) {
			fLexer.eatToken();
			String id = fLexer.readId();
			ud_type.setName(ud_type.getName() + "." + id);
		}
		
		return ud_type;		
	}
	
	private SVDBTypeInfo class_fwd_type() throws SVParseException {
		fLexer.eatToken();
		SVDBTypeInfoFwdDecl type_fwd = new SVDBTypeInfoFwdDecl("class", fLexer.readId());

		// TODO: this should be a real parse
		if (fLexer.peekOperator(OP.HASH)) {
			if (fLexer.peekOperator(OP.HASH)) {
				// scanner().unget_ch('#');
				// TODO: List<SVDBModIfcClassParam> params = fParamDeclParser.parse();
				// cls.getSuperParameters().addAll(params);
				fLexer.eatToken();
				if (fLexer.peekOperator(OP.LPAREN)) {
					fLexer.skipPastMatch("(", ")");
				} else {
					fLexer.eatToken();
				}
			}
		}
		
		return type_fwd;
	}
	
	public SVDBTypeInfo data_type_or_void(int qualifiers) throws SVParseException {
		if (fLexer.peekKeyword(KW.VOID)) {
			fLexer.eatToken();
			return new SVDBTypeInfoBuiltin("void");
		} else {
			return data_type(qualifiers);
		}
	}
	
	/**
	 * net_port_type ::= [net_type] data_type_or_implicit
	 * 
	 * @param qualifiers
	 * @param id
	 * @return
	 * @throws SVParseException
	 */
	public SVDBTypeInfo net_port_type(int qualifiers) throws SVParseException {
		if (fLexer.peekKeyword(NetTypeE)) {
			// TODO: should find a way to qualify the type (?)
			fLexer.eatToken();
		}
		
		return data_type(qualifiers);
	}
	
	public SVDBTypeInfo enum_type() throws SVParseException {
		fLexer.readKeyword(KW.ENUM);
		SVDBTypeInfoEnum type = null;
		
		// TODO: scan base type
		if (!fLexer.peekOperator(OP.LBRACE)) {
			/* SVDBTypeInfo base_type = */ data_type(0);
			
			// Forward declaration
			if (fLexer.peekOperator(OP.SEMICOLON)) {
				return new SVDBTypeInfoFwdDecl();
			} else {
				type = new SVDBTypeInfoEnum();
			}
		} else {
			type = new SVDBTypeInfoEnum();
		}
		
		fLexer.readOperator(OP.LBRACE);
		while (fLexer.peek() != null) {
			long loc = fLexer.getStartLocation();
			SVDBTypeInfoEnumerator enum_v = new SVDBTypeInfoEnumerator(fLexer.readId());
			enum_v.setLocation(loc);
			
			// TODO: is this really necessary ?
			if (fLexer.peekOperator(OP.LBRACKET)) {
				fLexer.skipPastMatch("[", "]");
			}
			
			if (fLexer.peekOperator(OP.EQ)) {
				fLexer.eatToken();
				// TODO: 
				enum_v.setExpr(parsers().exprParser().expression());
			}
			type.addEnumerator(enum_v);
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		fLexer.readOperator(OP.RBRACE);
		
		return type;
	}
	
	public void typedef(ISVDBAddChildItem parent) throws SVParseException {
		SVDBTypedefStmt typedef = null;

		// typedef <type> <name>;

		long start = fLexer.getStartLocation();
		fLexer.readKeyword(KW.TYPEDEF);
		SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
		
		if (type.getType() != SVDBItemType.TypeInfoFwdDecl) {
			if (fLexer.peekOperator(OP.SEMICOLON)) {
				// It's an anonymous forward declaration
				SVDBTypeInfoFwdDecl fd_type = new SVDBTypeInfoFwdDecl("<<Anonymous>>", type.getName());
				typedef = new SVDBTypedefStmt(fd_type, fd_type.getName());
				typedef.setLocation(start);
			} else {
				String id = fLexer.readId();

				// TODO: dimension
				if (fLexer.peekOperator(OP.LBRACKET)) {
					type.setArrayDim(var_dim());
				}

				typedef = new SVDBTypedefStmt(type, id);

				typedef.setLocation(start);
			}
		} else {
			typedef = new SVDBTypedefStmt(type, type.getName());
			typedef.setLocation(start);
		}

		fLexer.readOperator(OP.SEMICOLON);
		parent.addChildItem(typedef);
	}
	
	public List<SVDBVarDimItem> var_dim() throws SVParseException {
		List<SVDBVarDimItem> ret = new ArrayList<SVDBVarDimItem>();
		
		while (fLexer.peek() != null) {
			fLexer.readOperator(OP.LBRACKET);
			SVDBVarDimItem dim = new SVDBVarDimItem();

			if (fLexer.peekOperator(OP.RBRACKET)) {
				dim.setDimType(DimType.Unsized);
			} else if (fLexer.peekOperator(OP.DOLLAR)) {
				fLexer.eatToken();
				dim.setDimType(DimType.Queue);
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					dim.setExpr(parsers().exprParser().expression());
				}
			} else if (fLexer.peekOperator(OP.MUL)) {
				fLexer.eatToken();
				dim.setDimType(DimType.Associative);
			} else {
				SVToken first = fLexer.consumeToken();
				// TODO: seems ambiguous
				if (first.isNumber() || first.isOperator() || 
						(fLexer.peekOperator() && !fLexer.peekOperator(OP.HASH))) {
					// most likely a constant expression
					fLexer.ungetToken(first);
					dim.setDimType(DimType.Sized);

					// TODO: should be constant expression
					SVDBExpr expr = parsers().exprParser().expression();
					if (fLexer.peekOperator(OP.COLON)) {
						// range
						fLexer.eatToken();
						dim.setExpr(new SVDBRangeExpr(expr, fParsers.exprParser().expression()));
					} else {
						// single value
						dim.setExpr(expr);
					}
				} else {
					// Assume this is a data-type
					fLexer.ungetToken(first);
					dim.setDimType(DimType.Associative);
					dim.setTypeInfo(parsers().dataTypeParser().data_type(0));
				}
			}
			ret.add(dim);

			fLexer.readOperator(OP.RBRACKET);
			
			if (!fLexer.peekOperator(OP.LBRACKET)) {
				break;
			}
		}
		
		return ret;
	}

	public List<SVDBVarDimItem> vector_dim() throws SVParseException {
		List<SVDBVarDimItem> ret = new ArrayList<SVDBVarDimItem>();
		
		while (fLexer.peek() != null) {
			fLexer.readOperator(OP.LBRACKET);
			SVDBVarDimItem dim = new SVDBVarDimItem();
			dim.setDimType(DimType.Sized);

			if (fDebugEn) {
				debug("--> expression");
			}
			
			SVToken t1 = fLexer.consumeToken();
			SVToken t2 = fLexer.consumeToken();
			
			SVDBExpr expr;
			if ((t1 != null && t2 != null) && 
					(t1.isNumber() || t1.isIdentifier()) &&
					t2.isOperator(":", "]")) {
				fLexer.ungetToken(t2);
				if (t1.isNumber()) {
					expr = new SVDBLiteralExpr(t1.getImage());
				} else {
					expr = new SVDBIdentifierExpr(t1.getImage());
				}
			} else {
				fLexer.ungetToken(t2);
				fLexer.ungetToken(t1);
				expr = fParsers.exprParser().expression();
			}
			if (fDebugEn) {
				debug("<-- expression - " + fLexer.peek());
			}

			if (fLexer.peekOperator(OP.COLON)) {
				// range
				fLexer.eatToken();
				t1 = fLexer.consumeToken();
				t2 = fLexer.consumeToken();
				
				if ((t1 != null && t2 != null) && 
						(t1.isNumber() || t1.isIdentifier()) &&
						t2.isOperator("]")) {
					SVDBExpr rhs;
					fLexer.ungetToken(t2);
					if (t1.isNumber()) {
						rhs = new SVDBLiteralExpr(t1.getImage());
					} else {
						rhs = new SVDBIdentifierExpr(t1.getImage());
					}
					dim.setExpr(new SVDBRangeExpr(expr, rhs));
				} else {
					fLexer.ungetToken(t2);
					fLexer.ungetToken(t1);
					dim.setExpr(new SVDBRangeExpr(expr, fParsers.exprParser().expression()));
				}
			} else {
				// single value
				dim.setExpr(expr);
			}

			ret.add(dim);

			fLexer.readOperator(OP.RBRACKET);
	
			if (!fLexer.peekOperator(OP.LBRACKET)) {
				break;
			}
		}
		
		return ret;
	}

	public List<SVDBVarDimItem> packed_dim() throws SVParseException {
		List<SVDBVarDimItem> ret = new ArrayList<SVDBVarDimItem>();
		
		while (fLexer.peek() != null) {
			fLexer.readOperator(OP.LBRACKET);
			SVDBVarDimItem dim = new SVDBVarDimItem();

			if (fLexer.peekOperator(OP.RBRACKET)) {
				dim.setDimType(DimType.Unsized);
			} else {
				dim.setExpr(fParsers.exprParser().const_or_range_expression());
			}
			ret.add(dim);

			fLexer.readOperator(OP.RBRACKET);
			
			if (!fLexer.peekOperator(OP.LBRACKET)) {
				break;
			}
		}
		
		return ret;
	}

	private void struct_union_body(ISVDBAddChildItem parent) throws SVParseException {

		while (fLexer.peekKeyword(KW.PACKED, KW.SIGNED)) {
			fLexer.eatToken();
		}
		
		fLexer.readOperator(OP.LBRACE);
		
		do {
			long it_start = fLexer.getStartLocation();
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
			
			SVDBVarDeclStmt var = new SVDBVarDeclStmt(type, 0);
			var.setLocation(it_start);
			
			while (fLexer.peek() != null) {
				it_start = fLexer.getStartLocation();
				String name = fLexer.readId();
				
				SVDBVarDeclItem vi = new SVDBVarDeclItem(name);
				vi.setLocation(it_start);

				if (fLexer.peekOperator(OP.LBRACKET)) {
					vi.setArrayDim(var_dim());
				}
				
				if (fLexer.peekOperator(OP.EQ)) {
					fLexer.eatToken();
					vi.setInitExpr(fParsers.exprParser().expression());
				}
				var.addChildItem(vi);
				
				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			
			parent.addChildItem(var);
			fLexer.readOperator(OP.SEMICOLON);
							
		} while (fLexer.peek() != null && !fLexer.peekOperator(OP.RBRACE));
		
		fLexer.readOperator(OP.RBRACE);
	}
	
	public SVDBTypeInfoClassType class_type() throws SVParseException {
		SVDBTypeInfoClassType class_type = new SVDBTypeInfoClassType("");
		
		while (fLexer.peek() != null) {
			String id = fLexer.readId();
			SVDBTypeInfoClassItem class_item = new SVDBTypeInfoClassItem(id);
			class_type.addClassItem(class_item);
			
			if (fLexer.peekOperator(OP.HASH)) {
				SVDBParamValueAssignList param_assign = parsers().paramValueAssignParser().parse(true);
				class_item.setParamAssignList(param_assign);
			}
			
			if (fLexer.peekOperator(OP.COLON2)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		return class_type;
	}
}


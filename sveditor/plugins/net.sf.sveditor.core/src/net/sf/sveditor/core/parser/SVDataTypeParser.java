/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
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

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
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
import net.sf.sveditor.core.db.expr.SVDBRangeExpr;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem.DimType;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVDataTypeParser extends SVParserBase {
	public static final Set<String>			IntegerAtomType;
	public static final Set<String>			IntegerVectorType;
	public static final Set<String>			IntegerTypes;
	public static final Set<String>			NonIntegerType;
	public static final Set<String>			NetType;
	public static final Set<String>			BuiltInTypes;
	
	static {
		IntegerAtomType = new HashSet<String>();
		IntegerAtomType.add("byte");
		IntegerAtomType.add("shortint");
		IntegerAtomType.add("int");
		IntegerAtomType.add("longint");
		IntegerAtomType.add("integer");
		IntegerAtomType.add("time");
		IntegerAtomType.add("genvar"); // Treat genvar as an integer
		IntegerVectorType = new HashSet<String>();
		IntegerVectorType.add("bit");
		IntegerVectorType.add("logic");
		IntegerVectorType.add("reg");
		IntegerTypes = new HashSet<String>();
		IntegerTypes.addAll(IntegerAtomType);
		IntegerTypes.addAll(IntegerVectorType);
		
		NonIntegerType = new HashSet<String>();
		NonIntegerType.add("shortreal");
		NonIntegerType.add("real");
		NonIntegerType.add("realtime");
		
		NetType = new HashSet<String>();
		NetType.add("supply0");
		NetType.add("supply1");
		NetType.add("tri");
		NetType.add("triand");
		NetType.add("trior");
		NetType.add("trireg");
		NetType.add("tri0");
		NetType.add("tri1");
		NetType.add("uwire");
		NetType.add("wire");
		NetType.add("wand");
		NetType.add("wor");
		NetType.add("input");
		NetType.add("output");
		NetType.add("inout");
		
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

		if (fLexer.peekKeyword(IntegerVectorType)) {
			// integer_vector_type [signing] { packed_dimension }
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(fLexer.eatToken());
			
			// signing
			if (fLexer.peekKeyword("signed", "unsigned")) {
				builtin_type.setAttr(fLexer.peekKeyword("signed")?
						SVDBTypeInfoBuiltin.TypeAttr_Signed:
							SVDBTypeInfoBuiltin.TypeAttr_Unsigned);
				fLexer.eatToken();
			}
			
			while (fLexer.peekOperator("[")) {
				if (fDebugEn) {
					debug("  IntegerVectorType vector");
				}
				builtin_type.setArrayDim(vector_dim());
			}
			type = builtin_type;
		} else if (fLexer.peekKeyword(NetType)) {
			//	net_declaration
			//	13
			//	 ::= 
			//	net_type [ drive_strength | charge_strength ] [  vectored  |  scalared  ] 
			//	data_type_or_implicit [ delay3 ] list_of_net_decl_assignments ;  
			debug("NetType");
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(fLexer.eatToken());
			
			// Drive Strength
			if (fLexer.peekOperator("("))  {
				tok = fLexer.consumeToken();		// eat the (
				if (fLexer.peekOperator(SVKeywords.fStrength))  {
					// Have (<strength>, <strength>)
					String strength1 = fLexer.readKeyword(SVKeywords.fStrength);
					fLexer.readOperator(",");		// 
					String strength2 = fLexer.readKeyword(SVKeywords.fStrength);
					fLexer.readOperator(")");		//
					// TODO: Do something with the strengths
				} else {
					fLexer.ungetToken(tok);// restore the (
				}
			}
			// Array dimensions
			if (fLexer.peekOperator("[")) {
				if (fDebugEn) {
					debug("  vector type");
				}
				builtin_type.setVectorDim(vector_dim());
			}
			// Delay 3
			// #(mintypmax,mintypmax, mintypmax)
			if (fLexer.peekOperator("#"))  {
				// Time expression
				fParsers.exprParser().delay_expr(3);
				// TODO - What Do something with the Delay expression
			}
			type = builtin_type;
		} else if (fLexer.peekKeyword(IntegerAtomType)) {
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(fLexer.eatToken());
			
			if (fLexer.peekKeyword("signed", "unsigned")) {
				builtin_type.setAttr(fLexer.peekKeyword("signed")?
						SVDBTypeInfoBuiltin.TypeAttr_Signed:
							SVDBTypeInfoBuiltin.TypeAttr_Unsigned);
				fLexer.eatToken();
			}
			type = builtin_type;
		} else if (fLexer.peekKeyword(NonIntegerType)) {
			type = new SVDBTypeInfoBuiltin(fLexer.eatToken());
		} else if (fLexer.peekKeyword("struct", "union")) {
			tok = fLexer.readKeywordTok("struct", "union");
			if (tok.getImage().equals("union")) {
				// TODO: preserve?
				if (fLexer.peekKeyword("tagged")) {
					fLexer.eatToken();
				}
			}
			
			if (fLexer.peekKeyword("packed")) {
				// TODO: preserve?
				fLexer.eatToken(); 
			}
			
			if (fLexer.peekKeyword("signed", "unsigned")) {
				// TODO: preserve?
				fLexer.eatToken();
			}
			
			type = (tok.getImage().equals("union"))?new SVDBTypeInfoUnion():new SVDBTypeInfoStruct();
			struct_union_body((ISVDBAddChildItem)type);

			// TODO:
		} else if (fLexer.peekKeyword("enum")) {
			type = enum_type();
			type.setName("<<ANONYMOUS>>");
		} else if (fLexer.peekKeyword(BuiltInTypes)) {
			// string, chandle, etc
			type = new SVDBTypeInfoBuiltin(fLexer.eatToken());
		} else if (fLexer.peekKeyword("virtual") || (qualifiers & SVDBFieldItem.FieldAttr_Virtual) != 0) {
			if (fLexer.peekKeyword("virtual")) {
				fLexer.eatToken();
			}
			// virtual [interface] interface_identifier
			if (fLexer.peekKeyword("interface")) {
				// TODO: use this somehow (?)
				fLexer.eatToken();
			}
			tok = fLexer.readIdTok();
			SVDBTypeInfoUserDef ud_type = new SVDBTypeInfoUserDef(tok.getImage());
			if (fLexer.peekOperator("#")) {
				SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse(true);
				ud_type.setParameters(plist);
			}
			
			// May be referring to the modport
			if (fLexer.peekOperator(".")) {
				fLexer.eatToken();
				String id = fLexer.readId();
				ud_type.setName(ud_type.getName() + "." + id);
			}
			
			type = ud_type;
		} else if (fLexer.peekKeyword("type")) {
			// type_reference ::=
			//   type ( expression )
			//   type ( data_type )
			type = new SVDBTypeInfoBuiltin(fLexer.eatToken());
			// TODO: skip paren expression
			error("'type' expression unsupported");
		} else if (fLexer.peekKeyword("class")) {
			// Class type
			fLexer.eatToken();
			SVDBTypeInfoFwdDecl type_fwd = new SVDBTypeInfoFwdDecl("class", fLexer.readId());

			// TODO: this should be a real parse
			if (fLexer.peekOperator("#")) {
				if (fLexer.peekOperator("#")) {
					// scanner().unget_ch('#');
					// TODO: List<SVDBModIfcClassParam> params = fParamDeclParser.parse();
					// cls.getSuperParameters().addAll(params);
					fLexer.eatToken();
					if (fLexer.peekOperator("(")) {
						fLexer.skipPastMatch("(", ")");
					} else {
						fLexer.eatToken();
					}
				}
			}
			type = type_fwd;
		} else if (fLexer.peekOperator("[") || fLexer.peekKeyword("signed", "unsigned")) {
			// Implicit items
			SVToken id = fLexer.consumeToken();
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(
					(id.getImage().equals("["))?"bit":id.getImage());
			
			// Implicit sized item
			
			debug("implicit type - " + id.getImage());

			if (id.getImage().equals("[")) {
				fLexer.ungetToken(id);
				builtin_type.setVectorDim(vector_dim());
			} else if (fLexer.peekOperator("[")) {
				builtin_type.setVectorDim(vector_dim());
			}
			
			type = builtin_type;
		} else if (SVKeywords.isVKeyword(fLexer.peek()) && 
				!fLexer.peekKeyword("interface") && 
				!fLexer.peekKeyword(SVKeywords.fBuiltinGates)) {
			// ERROR: 
			error("Invalid type name \"" + fLexer.peek() + "\"");
		} else {
			String id = fLexer.eatToken();
			SVDBParamValueAssignList p_list = null;
			
			// Parameterized type?
			if (fLexer.peekOperator("#")) {
				fLexer.eatToken();
				// Read in parameter list
				p_list = parsers().paramValueAssignParser().parse(false);
			}
			
			// Should be a user-defined type
			if (fLexer.peekOperator("::")) {
				StringBuilder type_id = new StringBuilder();
				type_id.append(id);
				
				// scoped type
				// [class_scope | package_scope] type_identifier { packed_dimension }
				while (fLexer.peekOperator("::")) {
					type_id.append(fLexer.eatToken()); // ::
					type_id.append(fLexer.readId());
				}
				
				type = new SVDBTypeInfoUserDef(type_id.toString());
				
				if (fLexer.peekOperator("[")) {
					// TODO: packed_dimension
					type.setArrayDim(packed_dim());
				}
			} else if (fLexer.peekOperator(".")) {
				// Interface type: interface.modport
				StringBuilder type_id = new StringBuilder();
				type_id.append(id);
				
				while (fLexer.peekOperator(".")) {
					type_id.append(fLexer.eatToken()); // .
					type_id.append(fLexer.readId());
				}
				
				type = new SVDBTypeInfoUserDef(type_id.toString());
			} else {
				type = new SVDBTypeInfoUserDef(id);
			}
			
			((SVDBTypeInfoUserDef)type).setParameters(p_list);
			
			if (fLexer.peekOperator("#")) {
				SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse(true);
				((SVDBTypeInfoUserDef)type).setParameters(plist);
			}
			
			// A sized enum is allowed to have a duplicate bit-width assigned
			if (fLexer.peekOperator("[")) {
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
	
	public SVDBTypeInfo data_type_or_void(int qualifiers) throws SVParseException {
		if (fLexer.peekOperator("void")) {
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
		if (fLexer.peekKeyword(NetType)) {
			// TODO: should find a way to qualify the type (?)
			fLexer.eatToken();
		}
		
		return data_type(qualifiers);
	}
	
	public SVDBTypeInfo enum_type() throws SVParseException {
		fLexer.readKeyword("enum");
		SVDBTypeInfoEnum type = null;
		
		// TODO: scan base type
		if (!fLexer.peekOperator("{")) {
			/* SVDBTypeInfo base_type = */ data_type(0);
			
			// Forward declaration
			if (fLexer.peekOperator(";")) {
				return new SVDBTypeInfoFwdDecl();
			} else {
				type = new SVDBTypeInfoEnum();
			}
		} else {
			type = new SVDBTypeInfoEnum();
		}
		
		fLexer.readOperator("{");
		while (fLexer.peek() != null) {
			SVDBLocation loc = fLexer.getStartLocation();
			SVDBTypeInfoEnumerator enum_v = new SVDBTypeInfoEnumerator(fLexer.readId());
			enum_v.setLocation(loc);
			
			// TODO: is this really necessary ?
			if (fLexer.peekOperator("[")) {
				fLexer.skipPastMatch("[", "]");
			}
			
			if (fLexer.peekOperator("=")) {
				fLexer.eatToken();
				// TODO: 
				enum_v.setExpr(parsers().exprParser().expression());
			}
			type.addEnumerator(enum_v);
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		fLexer.readOperator("}");
		
		return type;
	}
	
	public void typedef(ISVDBAddChildItem parent) throws SVParseException {
		SVDBTypedefStmt typedef = null;

		// typedef <type> <name>;

		SVDBLocation start = fLexer.getStartLocation();
		fLexer.readKeyword("typedef");
		SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
		
		if (type.getType() != SVDBItemType.TypeInfoFwdDecl) {
			if (fLexer.peekOperator(";")) {
				// It's an anonymous forward declaration
				SVDBTypeInfoFwdDecl fd_type = new SVDBTypeInfoFwdDecl("<<Anonymous>>", type.getName());
				typedef = new SVDBTypedefStmt(fd_type, fd_type.getName());
				typedef.setLocation(start);
			} else {
				String id = fLexer.readId();

				// TODO: dimension
				if (fLexer.peekOperator("[")) {
					type.setArrayDim(var_dim());
				}

				typedef = new SVDBTypedefStmt(type, id);

				typedef.setLocation(start);
			}
		} else {
			typedef = new SVDBTypedefStmt(type, type.getName());
			typedef.setLocation(start);
		}

		fLexer.readOperator(";");
		parent.addChildItem(typedef);
	}
	
	public List<SVDBVarDimItem> var_dim() throws SVParseException {
		List<SVDBVarDimItem> ret = new ArrayList<SVDBVarDimItem>();
		
		while (fLexer.peek() != null) {
			fLexer.readOperator("[");
			SVDBVarDimItem dim = new SVDBVarDimItem();

			if (fLexer.peekOperator("]")) {
				dim.setDimType(DimType.Unsized);
			} else if (fLexer.peekOperator("$")) {
				fLexer.eatToken();
				dim.setDimType(DimType.Queue);
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					dim.setExpr(parsers().exprParser().expression());
				}
			} else if (fLexer.peekOperator("*")) {
				fLexer.eatToken();
				dim.setDimType(DimType.Associative);
			} else {
				SVToken first = fLexer.consumeToken();
				// TODO: seems ambiguous
				if (first.isNumber() || first.isOperator() || 
						(fLexer.peekOperator() && !fLexer.peekOperator("#"))) {
					// most likely a constant expression
					fLexer.ungetToken(first);
					dim.setDimType(DimType.Sized);

					// TODO: should be constant expression
					SVDBExpr expr = parsers().exprParser().expression();
					if (fLexer.peekOperator(":")) {
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

			fLexer.readOperator("]");
			
			if (!fLexer.peekOperator("[")) {
				break;
			}
		}
		
		return ret;
	}

	public List<SVDBVarDimItem> vector_dim() throws SVParseException {
		List<SVDBVarDimItem> ret = new ArrayList<SVDBVarDimItem>();
		
		while (fLexer.peek() != null) {
			fLexer.readOperator("[");
			SVDBVarDimItem dim = new SVDBVarDimItem();
			dim.setDimType(DimType.Sized);

			debug("--> expression");
			SVDBExpr expr = parsers().exprParser().expression();
			debug("<-- expression - " + fLexer.peek());

			if (fLexer.peekOperator(":")) {
				// range
				fLexer.eatToken();
				dim.setExpr(new SVDBRangeExpr(expr, fParsers.exprParser().expression()));
			} else {
				// single value
				dim.setExpr(expr);
			}

			ret.add(dim);

			fLexer.readOperator("]");
	
			if (!fLexer.peekOperator("[")) {
				break;
			}
		}
		
		return ret;
	}

	public List<SVDBVarDimItem> packed_dim() throws SVParseException {
		List<SVDBVarDimItem> ret = new ArrayList<SVDBVarDimItem>();
		
		while (fLexer.peek() != null) {
			fLexer.readOperator("[");
			SVDBVarDimItem dim = new SVDBVarDimItem();

			if (fLexer.peekOperator("]")) {
				dim.setDimType(DimType.Unsized);
			} else {
				dim.setExpr(fParsers.exprParser().const_or_range_expression());
			}
			ret.add(dim);

			fLexer.readOperator("]");
			
			if (!fLexer.peekOperator("[")) {
				break;
			}
		}
		
		return ret;
	}

	private void struct_union_body(ISVDBAddChildItem parent) throws SVParseException {

		if (fLexer.peekKeyword("packed")) {
			fLexer.eatToken();
		}
		
		// TODO: signing
		
		fLexer.readOperator("{");
		
		do {
			SVDBLocation it_start = fLexer.getStartLocation();
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(0);
			
			SVDBVarDeclStmt var = new SVDBVarDeclStmt(type, 0);
			var.setLocation(it_start);
			
			while (fLexer.peek() != null) {
				it_start = fLexer.getStartLocation();
				String name = fLexer.readId();
				
				SVDBVarDeclItem vi = new SVDBVarDeclItem(name);
				vi.setLocation(it_start);

				if (fLexer.peekOperator("[")) {
					vi.setArrayDim(var_dim());
				}
				
				if (fLexer.peekOperator("=")) {
					fLexer.eatToken();
					vi.setInitExpr(fParsers.exprParser().expression());
				}
				var.addChildItem(vi);
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			
			parent.addChildItem(var);
			fLexer.readOperator(";");
							
		} while (fLexer.peek() != null && !fLexer.peekOperator("}"));
		
		fLexer.readOperator("}");
	}
	
	public SVDBTypeInfoClassType class_type() throws SVParseException {
		SVDBTypeInfoClassType class_type = new SVDBTypeInfoClassType("");
		
		while (fLexer.peek() != null) {
			String id = fLexer.readId();
			SVDBTypeInfoClassItem class_item = new SVDBTypeInfoClassItem(id);
			class_type.addClassItem(class_item);
			
			if (fLexer.peekOperator("#")) {
				SVDBParamValueAssignList param_assign = parsers().paramValueAssignParser().parse(true);
				class_item.setParamAssignList(param_assign);
			}
			
			if (fLexer.peekOperator("::")) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		return class_type;
	}
}


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

import java.util.HashSet;
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
import net.sf.sveditor.core.db.SVDBTypeInfoFwdDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;
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
				// TODO: packed_dimension
				fLexer.skipPastMatch("[", "]");
			}
			type = builtin_type;
		} else if (fLexer.peekKeyword(NetType)) {
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(fLexer.eatToken());
			
			if (fLexer.peekOperator("[")) {
				fLexer.startCapture();
				while (fLexer.peekOperator("[")) {
					fLexer.skipPastMatch("[", "]");
				}
				builtin_type.setVectorDim(fLexer.endCapture());
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
			String id = fLexer.readKeyword("struct", "union");
			if (id.equals("union")) {
				if (fLexer.peekKeyword("tagged")) {
					fLexer.eatToken();
				}
			} else {
				type = struct_body();
			}
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
			SVDBTypeInfoUserDef ud_type = new SVDBTypeInfoUserDef(fLexer.readId());
			if (fLexer.peekOperator("#")) {
				SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse(true);
				ud_type.setParameters(plist);
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
			String id = fLexer.eatToken();
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(
					(id.equals("["))?"bit":id);
			
			// Implicit sized item

			if (id.equals("[")) {
				fLexer.startCapture();
				do {
					fLexer.skipPastMatch("[", "]");
				} while (fLexer.peekOperator("["));
				builtin_type.setVectorDim(fLexer.endCapture());
			} else if (fLexer.peekOperator("[")) {
				fLexer.startCapture();
				do {
					fLexer.skipPastMatch("[", "]");
				} while (fLexer.peekOperator("["));
				builtin_type.setVectorDim(fLexer.endCapture());
			}
			
			type = builtin_type;
		} else if (SVKeywords.isVKeyword(fLexer.peek()) && 
				!fLexer.peekKeyword("interface") && 
				!fLexer.peekKeyword(SVKeywords.fBuiltinGates)) {
			// ERROR: 
			error("Invalid type name \"" + fLexer.peek() + "\"");
		} else {
			String id = fLexer.eatToken();
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
					
					// TODO: handle multi-dimensional vectors
					while (fLexer.peekOperator("[")) {
						fLexer.skipPastMatch("[", "]");
					}
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
			
			if (fLexer.peekOperator("#")) {
				SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse(true);
				((SVDBTypeInfoUserDef)type).setParameters(plist);
			}
			
			// A sized enum is allowed to have a duplicate bit-width assigned
			if (fLexer.peekOperator("[")) {
				fLexer.skipPastMatch("[", "]");
			}
		}
		
		if (type == null) {
			error("Unknown type starting with \"" + fLexer.peek() + "\"");
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
		boolean vals_specified = false;
		String val_str = null;
		int index = 0;
		
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
			String name = fLexer.readId();
			if (fLexer.peekOperator("[")) {
				fLexer.skipPastMatch("[", "]");
			}
			if (fLexer.peekOperator("=")) {
				fLexer.eatToken();
				// TODO: 
				val_str = parsers().exprParser().expression().toString();
				vals_specified = true;
			}
			type.addEnumValue(name, ((vals_specified)?""+index:val_str));
			
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
			String id = fLexer.readId();

			// TODO: dimension
			if (fLexer.peekOperator("[")) {
				fLexer.skipPastMatch("[", "]");
			}

			typedef = new SVDBTypedefStmt(type, id);

			typedef.setLocation(start);
			/*
				if (fScopeStack.size() > 0) {
					fScopeStack.peek().addItem(typedef);
				}
			 */
		} else {
			typedef = new SVDBTypedefStmt(type, type.getName());
			typedef.setLocation(start);
		}

		fLexer.readOperator(";");
		parent.addChildItem(typedef);
	}
	
	public SVDBVarDimItem var_dim() throws SVParseException {
		SVDBVarDimItem ret = new SVDBVarDimItem();
		
		fLexer.readOperator("[");
		
		if (fLexer.peekOperator("]")) {
			ret.setDimType(DimType.Unsized);
		} else if (fLexer.peekOperator("$")) {
			fLexer.eatToken();
			ret.setDimType(DimType.Queue);
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				ret.setExpr(parsers().exprParser().expression());
			}
		} else if (fLexer.peekOperator("*")) {
			fLexer.eatToken();
			ret.setDimType(DimType.Associative);
		} else {
			SVToken first = fLexer.consumeToken();
			// TODO: seems ambiguous
			if (first.isNumber() || first.isOperator() || 
					(fLexer.peekOperator() && !fLexer.peekOperator("#"))) {
				// most likely a constant expression
				fLexer.ungetToken(first);
				ret.setDimType(DimType.Sized);
				
				// TODO: should be constant expression
				SVDBExpr expr = parsers().exprParser().expression();
				if (fLexer.peekOperator(":")) {
					// range
					fLexer.eatToken();
					ret.setExpr(new SVDBRangeExpr(expr, fParsers.exprParser().expression()));
				} else {
					// single value
					ret.setExpr(expr);
				}
			} else {
				// Assume this is a data-type
				fLexer.ungetToken(first);
				ret.setDimType(DimType.Associative);
				ret.setTypeInfo(parsers().dataTypeParser().data_type(0));
			}
		}
		
		fLexer.readOperator("]");
		
		return ret;
	}

	private SVDBTypeInfoStruct struct_body() throws SVParseException {
		SVDBTypeInfoStruct struct = new SVDBTypeInfoStruct();

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
				var.addChildItem(vi);
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			
			struct.addChildItem(var);
			fLexer.readOperator(";");
							
		} while (fLexer.peek() != null && !fLexer.peekOperator("}"));
		
		fLexer.readOperator("}");
		
		return struct;
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


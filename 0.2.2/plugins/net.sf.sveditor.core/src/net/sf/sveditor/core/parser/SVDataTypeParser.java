package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoFwdDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
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
	
	public SVDBTypeInfo data_type(int qualifiers, String id) throws SVParseException {
		SVDBTypeInfo type = null;
		
		if (IntegerVectorType.contains(id)) {
			// integer_vector_type [signing] { packed_dimension }
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(id);
			
			// signing
			if (lexer().peekKeyword("signed", "unsigned")) {
				builtin_type.setAttr(lexer().peekKeyword("signed")?
						SVDBTypeInfoBuiltin.TypeAttr_Signed:
							SVDBTypeInfoBuiltin.TypeAttr_Unsigned);
				lexer().eatToken();
			}
			
			while (lexer().peekOperator("[")) {
				// TODO: packed_dimension
				lexer().skipPastMatch("[", "]");
			}
			type = builtin_type;
		} else if (NetType.contains(id)) {
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(id);
			
			if (lexer().peekOperator("[")) {
				lexer().startCapture();
				lexer().skipPastMatch("[", "]");
				builtin_type.setVectorDim(lexer().endCapture());
			}
			type = builtin_type;
		} else if (IntegerAtomType.contains(id)) {
			SVDBTypeInfoBuiltin builtin_type = new SVDBTypeInfoBuiltin(id);
			
			if (lexer().peekKeyword("signed", "unsigned")) {
				builtin_type.setAttr(lexer().peekKeyword("signed")?
						SVDBTypeInfoBuiltin.TypeAttr_Signed:
							SVDBTypeInfoBuiltin.TypeAttr_Unsigned);
				lexer().eatToken();
			}
			type = builtin_type;
		} else if (NonIntegerType.contains(id)) {
			type = new SVDBTypeInfoBuiltin(id);
		} else if (id.equals("struct") || id.equals("union")) {
			if (id.equals("union")) {
				if (lexer().peekKeyword("tagged")) {
					lexer().eatToken();
				}
			} else {
				type = struct_body();
			}
			// TODO:
		} else if (id.equals("enum")) {
			type = enum_type();
			type.setName("<<ANONYMOUS>>");
		} else if (BuiltInTypes.contains(id)) {
			// string, chandle, etc
			type = new SVDBTypeInfoBuiltin(id);
		} else if (id.equals("virtual") || (qualifiers & SVDBFieldItem.FieldAttr_Virtual) != 0) {
			// virtual [interface] interface_identifier
			SVDBTypeInfoUserDef ud_type = new SVDBTypeInfoUserDef(lexer().readId());
			if (lexer().peekOperator("#")) {
				SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse();
				ud_type.setParameters(plist);
			}
			type = ud_type;
		} else if (id.equals("type")) {
			// type_reference ::=
			//   type ( expression )
			//   type ( data_type )
			type = new SVDBTypeInfoBuiltin(id);
			// TODO: skip paren expression
			error("'type' expression unsupported");
		} else if (id.equals("class")) {
			// Class type
			SVDBTypeInfoFwdDecl type_fwd = new SVDBTypeInfoFwdDecl("class", lexer().readId());

			// TODO: this should be a real parse
			if (lexer().peekOperator("#")) {
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
			type = type_fwd;
		} else if (SVKeywords.isSVKeyword(id)) {
			// ERROR: 
			error("Invalid type name \"" + id + "\"");
		} else {
			// Should be a user-defined type
			if (lexer().peekOperator("::")) {
				lexer().eatToken();
				
				// scoped type
				// [class_scope | package_scope] type_identifier { packed_dimension }
				String type_id = lexer().readId();
				type = new SVDBTypeInfoUserDef(id + "::" + type_id, SVDBDataType.UserDefined);
				
				if (lexer().peekOperator("[")) {
					// TODO: packed_dimension
				}
			} else {
				type = new SVDBTypeInfoUserDef(id, SVDBDataType.UserDefined);
			}
			
			if (lexer().peekOperator("#")) {
				SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse();
				((SVDBTypeInfoUserDef)type).setParameters(plist);
			}
		}
		
		if (type == null) {
			error("Unknown type starting with \"" + id + "\"");
		}
		
		return type;
	}
	
	public SVDBTypeInfo data_type_or_void(int qualifiers, String id) throws SVParseException {
		if (id.equals("void")) {
			return new SVDBTypeInfoBuiltin("void");
		} else {
			return data_type(qualifiers, id);
		}
	}
	
	public SVDBTypeInfoEnum enum_type() throws SVParseException {
		SVDBTypeInfoEnum type = new SVDBTypeInfoEnum("");
		boolean vals_specified = false;
		String val_str = null;
		int index = 0;
		
		// TODO: scan base type
		if (!lexer().peekOperator("{")) {
			data_type(0, lexer().eatToken());
		}
		
		lexer().readOperator("{");
		while (lexer().peek() != null) {
			String name = lexer().readId();
			if (lexer().peekOperator("[")) {
				lexer().skipPastMatch("[", "]");
			}
			if (lexer().peekOperator("=")) {
				lexer().eatToken();
				val_str = parsers().SVParser().readExpression();
				vals_specified = true;
			}
			type.addEnumValue(name, ((vals_specified)?""+index:val_str));
			
			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			} else {
				break;
			}
		}
		lexer().readOperator("}");
		
		return type;
	}

	private SVDBTypeInfoStruct struct_body() throws SVParseException {
		SVDBTypeInfoStruct struct = new SVDBTypeInfoStruct();

		if (lexer().peekKeyword("packed")) {
			lexer().eatToken();
		}
		
		// TODO: signing
		
		lexer().readOperator("{");
		
		do {
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(
					0, lexer().readIdOrKeyword());
			
			while (lexer().peek() != null) {
				String name = lexer().readId();
				int attr = 0;
				String bounds = null;
				
				if (lexer().peekOperator("[")) {
					// Read array data-type
					lexer().eatToken();
					
					// array or queue
					if (lexer().peekOperator("$")) {
						// queue
						lexer().eatToken();
						lexer().readOperator("]");
						attr |= SVDBVarDeclItem.VarAttr_Queue;
					} else if (lexer().peekOperator("]")) {
						lexer().readOperator("]");
						attr |= SVDBVarDeclItem.VarAttr_DynamicArray;
					} else {
						// bounded array
						lexer().startCapture();
						lexer().skipPastMatch("[", "]");
						bounds = lexer().endCapture();
						attr |= SVDBVarDeclItem.VarAttr_FixedArray;
					}
				}
				
				SVDBVarDeclItem var = new SVDBVarDeclItem(type, name, attr);
				
				if (bounds != null) {
					var.setArrayDim(bounds);
				}
				
				struct.getFields().add(var);
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
			lexer().readOperator(";");
							
		} while (lexer().peek() != null && !lexer().peekOperator("}"));
		
		lexer().readOperator("}");
		
		return struct;
	}
}


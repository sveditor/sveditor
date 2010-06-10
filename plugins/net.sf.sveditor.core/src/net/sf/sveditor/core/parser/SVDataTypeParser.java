package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
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
		
		BuiltInTypes = new HashSet<String>();
		BuiltInTypes.add("string");
		BuiltInTypes.add("chandle");
		BuiltInTypes.add("event");
	}
	
	public SVDataTypeParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBTypeInfo data_type(String id) throws SVParseException {
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
			
			if (lexer().peekOperator("[")) {
				// TODO: packed_dimension
				lexer().skipPastMatch("[", "]");
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
			}
			// TODO:
		} else if (id.equals("enum")) {
			lexer().parseException("enum type currently unsupported");
		} else if (BuiltInTypes.contains(id)) {
			// string, chandle, etc
			type = new SVDBTypeInfoBuiltin(id);
		} else if (id.equals("virtual")) {
			// virtual [interface] interface_identifier
		} else if (id.equals("type")) {
			// type_reference ::=
			//   type ( expression )
			//   type ( data_type )
			type = new SVDBTypeInfoBuiltin(id);
			// TODO: skip paren expression
			lexer().parseException("'type' expression unsupported");
		} else if (SVKeywords.isSVKeyword(id)) {
			// ERROR: 
			lexer().parseException("Invalid type name \"" + id + "\"");
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
			lexer().parseException("Unknown type starting with \"" + id + "\"");
		}
		
		return type;
	}
	
	public SVDBTypeInfo data_type_or_void(String id) throws SVParseException {
		if (id.equals("void")) {
			return new SVDBTypeInfoBuiltin("void");
		} else {
			return data_type(id);
		}
	}

}

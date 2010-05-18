package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanner.SVTypeInfo;

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
			type = new SVDBTypeInfo(id, 0);
			
			// signing
			if (lexer().peekKeyword("signed", "unsigned")) {
				type.setAttr(lexer().peekKeyword("signed")?
						SVDBTypeInfo.TypeAttr_Signed:
							SVDBTypeInfo.TypeAttr_Unsigned);
				lexer().eatToken();
			}
			
			if (lexer().peekOperator("[")) {
				// TODO: packed_dimension
			}
		} else if (IntegerAtomType.contains(id)) {
			type = new SVDBTypeInfo(id, 0);
			
			if (lexer().peekKeyword("signed", "unsigned")) {
				type.setAttr(lexer().peekKeyword("signed")?
						SVDBTypeInfo.TypeAttr_Signed:
							SVDBTypeInfo.TypeAttr_Unsigned);
				lexer().eatToken();
			}
		} else if (NonIntegerType.contains(id)) {
			type = new SVDBTypeInfo(id, 0);
		} else if (id.equals("struct") || id.equals("union")) {
			if (id.equals("union")) {
				if (lexer().peekKeyword("tagged")) {
					lexer().eatToken();
				}
			}
			// TODO:
		} else if (id.equals("enum")) {
		} else if (BuiltInTypes.contains(id)) {
			// string, chandle, etc
			type = new SVDBTypeInfo(id, 0);
		} else if (id.equals("virtual")) {
			// virtual [interface] interface_identifier
		} else if (id.equals("type")) {
			// type_reference ::=
			//   type ( expression )
			//   type ( data_type )
			type = new SVDBTypeInfo(id, 0);
			// TODO: skip paren expression
		} else if (SVKeywords.isSVKeyword(id)) {
			// ERROR: 
			throw new SVParseException("Invalid type name \"" + id + "\"");
		} else {
			// Should be a user-defined type
			if (lexer().peekOperator("::")) {
				lexer().eatToken();
				
				// scoped type
				// [class_scope | package_scope] type_identifier { packed_dimension }
				String type_id = lexer().readId();
				type = new SVDBTypeInfo(id + "::" + type_id, 0);
				
				if (lexer().peekOperator("[")) {
					// TODO: packed_dimension
				}
			} else {
				type = new SVDBTypeInfo(id, 0);
			}
		}
		
		if (type == null) {
			throw new SVParseException("Unknown type starting with \"" + id + "\"");
		}
		
		return type;
	}
	
	public SVDBTypeInfo data_type_or_void(String id) throws SVParseException {
		if (id.equals("void")) {
			return new SVDBTypeInfo("void", 0);
		} else {
			return data_type(id);
		}
	}

}

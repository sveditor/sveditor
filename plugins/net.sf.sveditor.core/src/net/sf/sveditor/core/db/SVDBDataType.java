package net.sf.sveditor.core.db;

public enum SVDBDataType {
	// Variables and fields are either of 
	// ModuleIfc, UserDefined, or BuiltIn type 
	ModuleIfc,
	UserDefined,
	FwdDecl, // typedef <class|enum|union|struct>
	BuiltIn,
	WireBuiltin,

	// Typedefs can be of Enum, Struct, 
	// UserDefined, or BuiltIn type
	Enum,
	Struct
}

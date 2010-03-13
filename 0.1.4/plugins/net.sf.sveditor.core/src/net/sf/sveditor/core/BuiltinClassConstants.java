package net.sf.sveditor.core;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBItemType;


public class BuiltinClassConstants {
	
	public static final String Covergroup		= "__sv_builtin_covergroup";
	public static final String Coverpoint		= "__sv_builtin_coverpoint";
	public static final String CoverpointCross	= "__sv_builtin_coverpoint_cross";

	private static final Map<SVDBItemType, String>		fBaseClassMap;
	
	static {
		fBaseClassMap = new HashMap<SVDBItemType, String>();
		fBaseClassMap.put(SVDBItemType.Covergroup, Covergroup);
		fBaseClassMap.put(SVDBItemType.Coverpoint, Coverpoint);
	}
	
	public static boolean hasBuiltin(SVDBItemType type) {
		return fBaseClassMap.containsKey(type);
	}
	
	public static String getBuiltinClass(SVDBItemType type) {
		return fBaseClassMap.get(type);
	}

}

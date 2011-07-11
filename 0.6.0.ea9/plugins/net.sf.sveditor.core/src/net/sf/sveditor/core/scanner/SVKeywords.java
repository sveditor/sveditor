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


package net.sf.sveditor.core.scanner;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class SVKeywords {
	
	private static final String 		fKeywords[] = {
		"alias*",
		"always",
		"always_comb*",
		"always_ff*",
		"always_latch*",
		"and",
		"assert*",
		"assign",
		"assume*",
		"automatic",
		"before*",
		"begin",
		"bind*",
		"bins*",
		"binsof*",
		"bit*",
		"break*",
		"buf",
		"bufif0",
		"bufif1",
		"byte*",
		"case",
		"casex",
		"casez",
		"cell",
		"chandle*",
		"class*",
		"clocking*",
		"cmos",
		"config",
		"const*",
		"constraint*",
		"context*",
		"continue*",
		"cover*",
		"covergroup*",
		"coverpoint*",
		"cross*",
		"deassign",
		"default",
		"defparam",
		"design",
		"disable",
		"dist*",
		"do*",
		"edge",
		"else",
		"end",
		"endcase",
		"endclass*",
		"endclocking*",
		"endconfig",
		"endfunction",
		"endgenerate",
		"endgroup*",
		"endinterface*",
		"endmodule",
		"endpackage*",
		"endprimitive",
		"endprogram*",
		"endproperty*",
		"endspecify",
		"endsequence*",
		"endtable",
		"endtask",
		"enum*",
		"event",
		"expect*",
		"export*",
		"extends*",
		"extern*",
		"final*",
		"first_match*",
		"for",
		"force",
		"foreach*",
		"forever",
		"fork",
		"forkjoin*",
		"function",
		"generate",
		"genvar",
		"highz0",
		"highz1",
		"if",
		"iff*",
		"ifnone",
		"ignore_bins*",
		"illegal_bins*",
		"import*",
		"incdir",
		"include",
		"initial",
		"inout",
		"input",
		"inside*",
		"instance",
		"int*",
		"integer",
		"interface*",
		"intersect*",
		"join",
		"join_any*",
		"join_none*",
		"large",
		"liblist",
		"library",
		"local*",
		"localparam",
		"logic*",
		"longint*",
		"macromodule",
		"matches*",
		"medium",
		"modport*",
		"module",
		"nand",
		"negedge",
		"new*",
		"nmos",
		"nor",
		"noshowcancelled",
		"not",
		"notif0",
		"notif1",
		"null*",
		"or",
		"output",
		"package*",
		"packed*",
		"parameter",
		"pmos",
		"posedge",
		"primitive",
		"priority*",
		"program*",
		"property*",
		"protected*",
		"pull0",
		"pull1",
		"pulldown",
		"pullup",
		"pulsestyle_onevent",
		"pulsestyle_ondetect",
		"pure*",
		"rand*",
		"randc*",
		"randcase*",
		"randsequence*",
		"rcmos",
		"real",
		"realtime",
		"ref*",
		"reg",
		"release",
		"repeat",
		"return*",
		"rnmos",
		"rpmos",
		"rtran",
		"rtranif0",
		"rtranif1",
		"scalared",
		"sequence*",
		"shortint*",
		"shortreal*",
		"showcancelled",
		"signed",
		"small",
		"solve*",
		"specify",
		"specparam",
		"static*",
		"string*",
		"strong0",
		"strong1",
		"struct*",
		"super*",
		"supply0",
		"supply1",
		"table",
		"tagged*",
		"task",
		"this*",
		"throughout*",
		"time",
		"timeprecision*",
		"timeunit*",
		"tran",
		"tranif0",
		"tranif1",
		"tri",
		"tri0",
		"tri1",
		"triand",
		"trior",
		"trireg",
		"type*",
		"typedef*",
		"union*",
		"unique*",
		"unsigned",
		"use",
		"uwire",
		"var*",
		"vectored",
		"virtual*",
		"void*",
		"wait",
		"wait_order*",
		"wand",
		"weak0",
		"weak1",
		"while",
		"wildcard*",
		"wire",
		"with*",
		"within*",
		"wor",
		"xnor",
		"xor",
		
		// defacto-reserved words
		"1step"
	};
	
	private static final String 					fTypeStrings[] = {
		"void",
		"chandle",
		"event",
		
		"bit",
		"logic",
		"reg",
		
		"byte",
		"shortint",
		"int",
		"longint",
		"integer",
		"time",
		
		"shortreal",
		"real",
		"realtime",
		
		"signed",
		"string",
		"unsigned",
	};
	
	public static final Set<String>					fBuiltinTypes;
	public static final Set<String>					fTypePrefixes;
	public static final Set<String>					fBuiltinDeclTypes;
	private static final Map<String, Boolean>		fKeywordMap;
	public static final Set<String>					fBuiltinGates;
	public static final Set<String>					fStrength0;
	public static final Set<String>					fStrength1;
	public static final Set<String>					fStrength;
	public static final Set<String>					fAssignmentOps;
	
	static {
		fKeywordMap = new HashMap<String, Boolean>();
		
		for (String str : fKeywords) {
			boolean is_sv = str.endsWith("*");
			if (is_sv) {
				str = str.substring(0, str.length()-1);
			}
			fKeywordMap.put(str, is_sv);
		}
		
		fBuiltinTypes = new HashSet<String>();
		fBuiltinDeclTypes = new HashSet<String>();
		for (String n : fTypeStrings) {
			fBuiltinTypes.add(n);
			if (!n.equals("void")) {
				fBuiltinDeclTypes.add(n);
			}
		}
		
		fBuiltinGates = new HashSet<String>();
		fBuiltinGates.add("cmos");
		fBuiltinGates.add("rcmos");
		fBuiltinGates.add("bufif0");
		fBuiltinGates.add("bufif1");
		fBuiltinGates.add("notif0");
		fBuiltinGates.add("notif1");
		fBuiltinGates.add("nmos");
		fBuiltinGates.add("pmos");
		fBuiltinGates.add("rnmos");
		fBuiltinGates.add("rpmos");
		fBuiltinGates.add("and");
		fBuiltinGates.add("nand");
		fBuiltinGates.add("or");
		fBuiltinGates.add("nor");
		fBuiltinGates.add("xor");
		fBuiltinGates.add("xnor");
		fBuiltinGates.add("buf");
		fBuiltinGates.add("not");
		fBuiltinGates.add("tranif0");
		fBuiltinGates.add("tranif1");
		fBuiltinGates.add("rtranif1");
		fBuiltinGates.add("rtranif0");
		fBuiltinGates.add("tran");
		fBuiltinGates.add("rtran");
		fBuiltinGates.add("pullup");
		fBuiltinGates.add("pulldown");
		
		fTypePrefixes = new HashSet<String>();
		fTypePrefixes.add("const");
		fTypePrefixes.add("virtual");
		
		fStrength0 = new HashSet<String>();
		fStrength0.add("supply0");
		fStrength0.add("strong0");
		fStrength0.add("pull0");
		fStrength0.add("weak0");
		
		fStrength1 = new HashSet<String>();
		fStrength1.add("supply1");
		fStrength1.add("strong1");
		fStrength1.add("pull1");
		fStrength1.add("weak1");
		
		fStrength = new HashSet<String>();
		fStrength.addAll(fStrength0);
		fStrength.addAll(fStrength1);
		
		fAssignmentOps = new HashSet<String>();
		fAssignmentOps.add("=");
		fAssignmentOps.add("+=");
		fAssignmentOps.add("-=");
		fAssignmentOps.add("*=");
		fAssignmentOps.add("/=");
		fAssignmentOps.add("&=");
		fAssignmentOps.add("|=");
		fAssignmentOps.add("^=");
		fAssignmentOps.add("%=");
		fAssignmentOps.add("<<=");
		fAssignmentOps.add(">>=");
		fAssignmentOps.add("<<<=");
		fAssignmentOps.add(">>>=");
		fAssignmentOps.add("<=");
	};

	public static boolean isSVKeyword(String kw) {
		Boolean is_sv = fKeywordMap.get(kw);
		return (is_sv != null);
	}
	
	public static boolean isBuiltinGate(String kw) {
		return fBuiltinGates.contains(kw);
	}
	
	public static boolean isVKeyword(String kw) {
		Boolean is_sv = fKeywordMap.get(kw);
		return (is_sv != null && !is_sv.booleanValue());
	}
	
	public static boolean isBuiltInType(String type) {
		return fBuiltinTypes.contains(type);
	}
	
	public static boolean isDir(String dir) {
		return (dir.equals("input") ||
				dir.equals("output") ||
				dir.equals("inout"));
	}
	
	public static Set<String> getKeywords() {
		return fKeywordMap.keySet();
	}
}

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
		"soft",
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
		"unique0*",
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
	
	/**
	 * Any keywords that end with *, are SV specific
	 */
	private static final String                     fSystemCalls[] = {
		"$display",
		"$displayb",
		"$displayh",
		"$displayo",
		"$dumpfile",
		"$dumpvars",
		"$dumpall",
		"$dumpflush",
		"$dumplimit",
		"$dumpoff",
		"$dumpon",
		"$dumpports",
		"$dumpportsall",
		"$dumpportsflush",
		"$dumpportsoff",
		"$dumpportslimit",
		"$dumpportson",
		"$fclose",
		"$fdisplay",
		"$fdisplayb",
		"$fdisplayh",
		"$fdisplayo",
		"$feof",
		"$ferror",
		"$fflush",
		"$fgetc",
		"$fgets",
		"$fmonitor",
		"$fmonitorb",
		"$fmonitorh",
		"$fmonitoro",
		"$fopen",
		"$fread",
		"$fscanf",
		"$fseek",
		"$fstrobe",
		"$fstrobeb",
		"$fstrobeh",
		"$fstrobeo",
		"$ftell",
		"$fwrite",
		"$fwriteb",
		"$fwriteh",
		"$fwriteo",
		"$monitor",
		"$monitorb",
		"$monitorh",
		"$monitoro",
		"$monitoroff",
		"$monitoron",
		"$psprintf",
		"$readmemb",
		"$readmemh",
		"$rewind",
		"$sscanf",
		"$sformat",
		"$sformatf",
		"$strobe",
		"$strobeb",
		"$strobeh",
		"$strobeo",
		"$swrite",
		"$swriteb",
		"$swriteh",
		"$swriteo",
		"$test$plusargs",
		"$ungetc",
		"$value$plusargs",
		"$write",
		"$writeb",
		"$writeh",
		"$writememb",
		"$writememh",
		"$writeo",
		
		"$exit",
		"$stime",
		"$time",
		"$realtime",
		"$printtimescale",
		"$timeformat",
		"$bitstoreal",
		"$realtobits",
		"$bitstoshortreal",
		"$shortrealtobits",
		"$itor",
		"$rtoi",
		"$signed",
		"$unsigned",
		"$cast",
		"$bits",
		"$isunbounded",
		"$typename",
		"$unpacked_dimensions",
		"$dimensions",
		"$left",
		"$right",
		"$low",
		"$high",
		"$increment",
		"$size",
		"$clog2",
		"$asin",
		"$ln",
		"$acos",
		"$log10",
		"$atan",
		"$exp",
		"$atan2",
		"$sqrt",
		"$hypot",
		"$pow",
		"$sinh",
		"$floor",
		"$cosh",
		"$ceil",
		"$tanh",
		"$sin",
		"$asinh",
		"$cos",
		"$acosh",
		"$tan",
		"$atanh",
		"$fatal",
		"$error",
		"$warning",
		"$info",
		"$fatal",
		"$error",
		"$warning",
		"$info",
		"$asserton",
		"$assertoff",
		"$assertkill",
		"$assertpasson",
		"$assertpassoff",
		"$assertfailon",
		"$assertfailoff",
		"$assertnonvacuouson",
		"$assertvacuousoff",
		"$onehot",
		"$onehot0",
		"$isunknown",
		"$sampled",
		"$rose",
		"$fell",
		"$stable",
		"$changed",
		"$past",
		"$countones",
		"$past_gclk",
		"$rose_gclk",
		"$fell_gclk",
		"$stable_gclk",
		"$changed_gclk",
		"$future_gclk",
		"$rising_gclk",
		"$falling_gclk",
		"$steady_gclk",
		"$changing_gclk",
		"$coverage_control",
		"$coverage_get_max",
		"$coverage_get",
		"$coverage_merge",
		"$coverage_save",
		"$get_coverage",
		"$set_coverage_db_name",
		"$load_coverage_db",
		"$random",
		"$urandom",
		"$urandom_range",
		"$dist_chi_square",
		"$dist_erlang",
		"$dist_exponential",
		"$dist_normal",
		"$dist_poisson",
		"$dist_t",
		"$dist_uniform",
		"$q_initialize",
		"$q_add",
		"$q_remove",
		"$q_full",
		"$q_exam",
		"$async$and$array",
		"$async$and$plane",
		"$async$nand$array",
		"$async$nand$plane",
		"$async$or$array",
		"$async$or$plane",
		"$async$nor$array",
		"$async$nor$plane",
		"$sync$and$array",
		"$sync$and$plane",
		"$sync$nand$array",
		"$sync$nand$plane",
		"$sync$or$array",
		"$sync$or$plane",
		"$sync$nor$array",
		"$sync$nor$plane",
		"$system"
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
	private static final Map<String, Boolean>			fKeywordMap;
	public static final Set<String>					fBuiltinGates_with_Strength;
	public static final Set<String>					fBuiltinGates_no_Strength;
	public static final Set<String>					fBuiltinGates;
	public static final Set<String>					fStrength0;
	public static final Set<String>					fStrength1;
	public static final Set<String>					fStrengthC;
	public static final Set<String>					fStrength;
	public static final Set<String>					fAssignmentOps;
	public static final Set<String>					fBinaryOps;
	
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
		
		fBuiltinGates_with_Strength = new HashSet<String>();
		fBuiltinGates_with_Strength.add("cmos");
		fBuiltinGates_with_Strength.add("rcmos");
		fBuiltinGates_with_Strength.add("bufif0");
		fBuiltinGates_with_Strength.add("bufif1");
		fBuiltinGates_with_Strength.add("notif0");
		fBuiltinGates_with_Strength.add("notif1");
		fBuiltinGates_with_Strength.add("nmos");
		fBuiltinGates_with_Strength.add("pmos");
		fBuiltinGates_with_Strength.add("rnmos");
		fBuiltinGates_with_Strength.add("rpmos");
		fBuiltinGates_with_Strength.add("and");
		fBuiltinGates_with_Strength.add("nand");
		fBuiltinGates_with_Strength.add("or");
		fBuiltinGates_with_Strength.add("nor");
		fBuiltinGates_with_Strength.add("xor");
		fBuiltinGates_with_Strength.add("xnor");
		fBuiltinGates_with_Strength.add("buf");
		fBuiltinGates_with_Strength.add("not");
		fBuiltinGates_with_Strength.add("pullup");
		fBuiltinGates_with_Strength.add("pulldown");

		fBuiltinGates_no_Strength = new HashSet<String>();
		fBuiltinGates_no_Strength.add("tranif0");
		fBuiltinGates_no_Strength.add("tranif1");
		fBuiltinGates_no_Strength.add("rtranif1");
		fBuiltinGates_no_Strength.add("rtranif0");
		fBuiltinGates_no_Strength.add("tran");
		fBuiltinGates_no_Strength.add("rtran");

		fBuiltinGates = new HashSet<String>();
		fBuiltinGates.addAll(fBuiltinGates_with_Strength);
		fBuiltinGates.addAll(fBuiltinGates_no_Strength);

		fTypePrefixes = new HashSet<String>();
		fTypePrefixes.add("const");
		fTypePrefixes.add("virtual");
		
		fStrength0 = new HashSet<String>();
		fStrength0.add("supply0");
		fStrength0.add("strong0");
		fStrength0.add("pull0");
		fStrength0.add("weak0");
		fStrength0.add("highz0");
		
		fStrength1 = new HashSet<String>();
		fStrength1.add("supply1");
		fStrength1.add("strong1");
		fStrength1.add("pull1");
		fStrength1.add("weak1");
		fStrength1.add("highz1");

		fStrengthC = new HashSet<String>();		// capacitor sizes
		fStrengthC.add("large");
		fStrengthC.add("medium");
		fStrengthC.add("small");
		
		
		fStrength = new HashSet<String>();
		fStrength.addAll(fStrength0);
		fStrength.addAll(fStrength1);
		fStrength.addAll(fStrengthC);
		
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
		fAssignmentOps.add("->");				// force an event
		
		fBinaryOps = new HashSet<String>();
		for (String op : new String[] {"&", "&&", "|", "||", "-",
				"+", "%", "!", "*", "**", "/", "^", "^~", "~^", "~",
				"?", "<", "<<", "<=", "<<<", ">", ">>", ">=", ">>>", "=", "*=",
				"/=", "%=", "+=", "==", "!=", "-=", "<<=", ">>=", "<<<=", ">>>=",
				"&=", "^=", "|=", "===", "!==", "==?", "!=?", "--", "++", "~&", "~|", ":", "::"}) {
			fBinaryOps.add(op);
		}
	};

	/**
	 * Checks to see if SV specific keyword
	 * @param kw
	 * @return
	 */
	public static boolean isSVKeyword(String kw) {
		Boolean is_sv = fKeywordMap.get(kw);
		return (is_sv != null);
	}
	
	public static boolean isBuiltinGate(String kw) {
		return fBuiltinGates.contains(kw);
	}
	
	/**
	 * Checks to see if Verilog specific keyword
	 * @param kw
	 * @return
	 */
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

	public static String[] getSystemCalls() {
		return fSystemCalls;
	}
}

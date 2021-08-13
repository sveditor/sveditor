/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

public interface ISVKeywords {
	
	enum KW {
		ABOVE("above", false, true),
		ABS("abs", false, true),
		ABSDELAY("absdelay", false, true),
		ABSDELTA("absdelta", false, true),
		ACCESS("access", false, true),
		ACOS("acos", false, true),
		ACOSH("acosh", false, true),
		AC_STIM("ac_stim", false, true),
		ALIAS("alias", true),
		ALIASPARAM("aliasparam", false, true),
		ALWAYS("always"),
		ALWAYS_COMB("always_comb", true),
		ALWAYS_FF("always_ff", true),
		ALWAYS_LATCH("always_latch", true),
		ANALOG("analog", false, true),
		ANALYSIS("analysis", false, true),
		AND("and"),
		ASIN("asin", false, true),
		ASINH("asinh", false, true),
		ASSERT("assert", true),
		ASSIGN("assign"),
		ASSUME("assume", true),
		ATAN("atan", false, true),
		ATAN2("atan2", false, true),
		ATANH("atanh", false, true),
		AUTOMATIC("automatic"),
		BEFORE("before", true),
		BEGIN("begin"),
		BIND("bind", true),
		BINS("bins", true),
		BINSOF("binsof", true),
		BIT("bit", true),
		BRANCH("branch", false, true),
		BREAK("break", true),
		BUF("buf"),
		BUFIF0("bufif0"),
		BUFIF1("bufif1"),
		BYTE("byte", true),
		CASE("case"),
		CASEX("casex"),
		CASEZ("casez"),
		CEIL("ceil", false, true),
		CELL("cell"),
		CHANDLE("chandle", true),
		CLASS("class", true),
		CLOCKING("clocking", true),
		CMOS("cmos"),
		CONFIG("config"),
		CONST("const", true),
		CONSTRAINT("constraint", true),
		CONTEXT("context", true),
		CONTINUE("continue", true),
		CONNECT("connect", false, true),
		CONNECTMODULE("connectmodule", false, true),
		CONNECTRULES("connectrules", false, true),
		CONTINOUS("continuos", false, true),
		COS("cos", false, true),
		COSH("cosh", false, true),
		COVER("cover", true),
		COVERGROUP("covergroup", true),
		COVERPOINT("coverpoint", true),
		CROSS("cross", true, true), // shared with SV and AMS
		DDT("ddt", false, true),
		DDT_NATURE("ddt_nature", false, true),
		DDX("ddx", false, true),
		DISCIPLINE("discipline", false, true),
		DISCRETE("discrete", false, true),
		DEASSIGN("deassign"),
		DEFAULT("default"),
		DEFPARAM("defparam"),
		DESIGN("design"),
		DISABLE("disable"),
		DIST("dist", true),
		DO("do", true),
		DOMAIN("domain", false, true),
		DRIVER_UPDATE("driver_update", false, true),
		EDGE("edge"),
		ELSE("else"),
		END("end"),
		ENDCASE("endcase"),
		ENDCLASS("endclass", true),
		ENDCLOCKING("endclocking", true),
		ENDCONFIG("endconfig"),
		ENDCONNECTRULES("endconnectrules", false, true),
		ENDDISCIPLINE("enddiscipline", false, true),
		ENDFUNCTION("endfunction"),
		ENDGENERATE("endgenerate"),
		ENDGROUP("endgroup", true),
		ENDINTERFACE("endinterface", true),
		ENDMODULE("endmodule"),
		ENDNATURE("endnature", false, true),
		ENDPACKAGE("endpackage", true),
		ENDPARAMSET("endparamset", false, true),
		ENDPRIMITIVE("endprimitive"),
		ENDPROGRAM("endprogram", true),
		ENDPROPERTY("endproperty", true),
		ENDSPECIFY("endspecify"),
		ENDSEQUENCE("endsequence", true),
		ENDTABLE("endtable"),
		ENDTASK("endtask"),
		ENUM("enum", true),
		EVENT("event"),
		EXCLUDE("exclude", false, true),
		EXP("exp", false, true),
		EXPECT("expect", true),
		EXPORT("export", true),
		EXTENDS("extends", true),
		EXTERN("extern", true),
		FINAL("final", true),
		FINAL_STEP("final_step", false, true),
		FIRST_MATCH("first_match", true),
		FLICKER_NOISE("flicker_noise", false, true),
		FLOOR("floor", false, true),
		FLOW("flow", false, true),
		FOR("for"),
		FORCE("force"),
		FOREACH("foreach", true),
		FOREVER("forever"),
		FORK("fork"),
		FORKJOIN("forkjoin", true),
		FROM("from", false, true),
		FUNCTION("function"),
		GENERATE("generate"),
		GENVAR("genvar"),
		GLOBAL("global", true),
		GROUND("ground", false, true),
		HIGHZ0("highz0"),
		HIGHZ1("highz1"),
		HYPOT("hypot", false, true),
		IDT("idt", false, true),
		IDTMOD("idtmod", false, true),
		IDT_NATURE("idt_nature", false, true),
		IF("if"),
		IFF("iff", true),
		IFNONE("ifnone"),
		IGNORE_BINS("ignore_bins", true),
		ILLEGAL_BINS("illegal_bins", true),
		IMPLEMENTS("implements", true),
		IMPORT("import", true),
		IMPLIES("implies", true),
		INCDIR("incdir"),
		INCLUDE("include"),
		INF("inf", false, true),
		INITIAL("initial"),
		INITIAL_STEP("initial_step", false, true),
		INOUT("inout"),
		INPUT("input"),
		INSIDE("inside", true),
		INSTANCE("instance"),
		INT("int", true),
		INTEGER("integer"),
		INTERFACE("interface", true),
		INTERSECT("intersect", true),
		JOIN("join"),
		JOIN_ANY("join_any", true),
		JOIN_NONE("join_none", true),
		LAPLACE_ND("laplace_nd", false, true),
		LAPLACE_NP("laplace_np", false, true),
		LAPLACE_ZD("laplace_zd", false, true),
		LAPLACE_ZP("laplace_zp", false, true),
		LARGE("large"),
		LAST_CROSSING("last_crossing", false, true),
		LIBLIST("liblist"),
		LIBRARY("library"),
		LIMEXP("limexp", false, true),
		LN("ln", false, true),
		LOCAL("local", true),
		LOCALPARAM("localparam"),
		LOG("log", false, true),
		LOGIC("logic", true),
		LONGINT("longint", true),
		MACROMODULE("macromodule"),
		MAX("max", false, true),
		MATCHES("matches", true),
		MEDIUM("medium"),
		MERGED("merged", false, true),
		MIN("min", false, true),
		MODPORT("modport", true),
		MODULE("module"),
		NAND("nand"),
		NATURE("nature", false, true),
		NEGEDGE("negedge"),
		NET_RESOLUTION("net_resolution", false, true),
		NEW("new", true),
		NMOS("nmos"),
		NOISE_TABLE("noise_table", false, true),
		NOISE_TABLE_LOG("noise_table_log", false, true),
		NOR("nor"),
		NOSHOWCANCELLED("noshowcancelled"),
		NOT("not"),
		NOTIF0("notif0"),
		NOTIF1("notif1"),
		NULL("null", true),
		OR("or"),
		OUTPUT("output"),
		PACKAGE("package", true),
		PACKED("packed", true),
		PARAMETER("parameter"),
		PARAMSET("paramset", false, true),
		PMOS("pmos"),
		POSEDGE("posedge"),
		POTENTIAL("potential", false, true),
		POW("pow", false, true),
		PRIMITIVE("primitive"),
		PRIORITY("priority", true),
		PROGRAM("program", true),
		PROPERTY("property", true),
		PROTECTED("protected", true),
		PULL0("pull0"),
		PULL1("pull1"),
		PULLDOWN("pulldown"),
		PULLUP("pullup"),
		PULSESTYLE_ONEVENT("pulsestyle_onevent"),
		PULSESTYLE_ONDETECT("pulsestyle_ondetect"),
		PURE("pure", true),
		RAND("rand", true),
		RANDC("randc", true),
		RANDCASE("randcase", true),
		RANDSEQUENCE("randsequence", true),
		RCMOS("rcmos"),
		REAL("real"),
		REALTIME("realtime"),
		REF("ref", true),
		REG("reg"),
		RELEASE("release"),
		REPEAT("repeat"),
		RESOLVETO("resolveto", false, true),
		RESTRICT("restrict", true),
		RETURN("return", true),
		RNMOS("rnmos"),
		RPMOS("rpmos"),
		RTRAN("rtran"),
		RTRANIF0("rtranif0"),
		RTRANIF1("rtranif1"),
		S_UNTIL("s_until", true),
		S_UNTIL_WITH("s_until_with", true),
		SCALARED("scalared"),
		SIN("sin", false, true),
		SINH("sinh", false, true),
		SEQUENCE("sequence", true),
		SHORTINT("shortint", true),
		SHORTREAL("shortreal", true),
		SHOWCANCELLED("showcancelled"),
		SIGNED("signed"),
		SLEW("slew", false, true),
		SMALL("small"),
		SOFT("soft"), // isn't this a SV keyword?
		SOLVE("solve", true),
		SPECIFY("specify"),
		SPECPARAM("specparam"),
		SPLIT("split", false, true),
		SQRT("sqrt", false, true),
		STATIC("static", true),
		STRING("string", true, true), // Both SV and AMS
		STRONG("strong", true),
		STRONG0("strong0"),
		STRONG1("strong1"),
		STRUCT("struct", true),
		SUPER("super", true),
		SUPPLY0("supply0"),
		SUPPLY1("supply1"),
		TABLE("table"),
		TAN("tan", false, true),
		TANH("tanh", false, true),
		TAGGED("tagged", true),
		TASK("task"),
		THIS("this", true),
		THROUGHOUT("throughout", true),
		TIME("time"),
		TIMER("timer", false, true),
		TIMEPRECISION("timeprecision", true),
		TIMEUNIT("timeunit", true),
		TRAN("tran"),
		TRANIF0("tranif0"),
		TRANIF1("tranif1"),
		TRANSITION("transition", false, true),
		TRI("tri"),
		TRI0("tri0"),
		TRI1("tri1"),
		TRIAND("triand"),
		TRIOR("trior"),
		TRIREG("trireg"),
		TYPE("type", true),
		TYPEDEF("typedef", true),
		UNION("union", true),
		UNITS("units", false, true),
		UNIQUE("unique", true),
		UNIQUE0("unique0", true),
		UNSIGNED("unsigned"),
		USE("use"),
		UNTIL("until", true),
		UNTIL_WITH("until_with", true),
		UNTYPED("untyped", true),
		UWIRE("uwire"),
		VAR("var", true),
		VECTORED("vectored"),
		VIRTUAL("virtual", true),
		VOID("void", true),
		WAIT("wait"),
		WAIT_ORDER("wait_order", true),
		WAND("wand"),
		WEAK("weak", true),
		WEAK0("weak0"),
		WEAK1("weak1"),
		WHILE("while"),
		WHITE_NOISE("white_noise", false, true),
		WILDCARD("wildcard", true),
		WIRE("wire"),
		WITH("with", true),
		WITHIN("within", true),
		WOR("wor"),
		WREAL("wreal", true, true),
		XNOR("xnor"),
		XOR("xor"),
		ZI_ND("zi_nd", false, true),
		ZI_NP("zi_np", false, true),
		ZI_ZD("zi_zd", false, true),
		ZI_ZP("zi_zp", false, true),
		
		// defacto-reserved words
		ONE_STEP("1step", true);
		
		private String 		fImg;
		private boolean		fSV;  // SystemVerilog, and not Verilog
		private boolean		fAMS; // AMS and not Verilog
		
		KW(String img) {
			this(img, false, false);
		}
		
		KW(String img, boolean sv) {
			this(img, sv, false);
		}
		
		KW(String img, boolean sv, boolean ams) {
			fImg = img;
			fSV = sv;
			fAMS = ams;
		}
		
		public boolean isSV() { return fSV; }
		public boolean isAMS() { return fAMS; }
		public String getImg() { return fImg; }
		
		private static final Set<KW>	fSVKeywords;
		private static final Set<KW>	fVLKeywords;
		private static final Set<KW>	fAMSKeywords;
		
		static {
			fSVKeywords = new HashSet<KW>();
			fVLKeywords = new HashSet<KW>();
			fAMSKeywords = new HashSet<KW>();
			
			for (KW kw : KW.values()) {
				if (kw.isSV() || (!kw.isSV() && !kw.isAMS())) {
					fSVKeywords.add(kw);
				}
				if (!kw.isSV()) {
					fVLKeywords.add(kw);
				}
				if (kw.isAMS()) {
					fAMSKeywords.add(kw);
				}
			}
		}
		
		public static Set<KW> getSVKeywords() {
			return fSVKeywords;
		}
		
		public static Set<KW> getVLKeywords() {
			return fVLKeywords;
		}
		
		public static Set<KW> getAMSKeywords() {
			return fAMSKeywords;
		}
	}

}

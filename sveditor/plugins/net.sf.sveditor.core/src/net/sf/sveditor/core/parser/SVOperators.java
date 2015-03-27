package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

public class SVOperators {

	public static final String RelationalOps[] = { "&", "&&", "&&&", "|", "||", "-",
		"+", "%", "!", "*", "**", "/", "^", "^~", "~^", "~",
		"?", "<", "<<", "<=", "<<<", ">", ">>", ">=", ">>>", "=", "*=",
		"/=", "%=", "+=", "==", "!=", "-=", "<<=", ">>=", "<<<=", ">>>=",
		"&=", "^=", "|=", "===", "!==", "==?", "!=?"};
	
	public static final String ComparisonAssignOps[] = { 
		"<", "<=", ">", ">=", "=", "*=",
		"/=", "%=", "+=", "==", "!=", "-=", "<<=", ">>=", "<<<=", ">>>=",
		"&=", "^=", "|=", "===", "!==", "==?", "!=?"};

	public static final String GroupingOps[] = { "(", ")", "{", "}", "[", "]", };

	public static final String MiscOps[] = { ":", "::", ":/", ":=", "+:", "-:", // array-index
		// operators
		",", ";", ".", ".*", "'", "->", "->>", "-->", "#", "##", "@", "@@", "(*", "*)",
		// Assertion operators
		"=>", "|=>", "|->", "#-#", "#=#", 
		// Specify Operators
		/*"=>", already included*/ "+=>", "-=>", "*>", "-*>", "+*>",
		"--", "++"};

	public static final String AllOperators[];

	static {
		AllOperators = new String[RelationalOps.length + GroupingOps.length
		                          + MiscOps.length];
		int idx = 0;

		for (String o : RelationalOps) {
			AllOperators[idx++] = o;
		}

		for (String o : GroupingOps) {
			AllOperators[idx++] = o;
		}

		for (String o : MiscOps) {
			AllOperators[idx++] = o;
		}
	}
	
	public static final Set<String>					fAssignmentOps;

	static {
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
//		fAssignmentOps.add("->");				// force an event		
	}
	
	public static final Set<String>					fBinaryOps;
	
	static {
		fBinaryOps = new HashSet<String>();
		for (String op : new String[] {"&", "&&", "|", "||", "-",
				"+", "%", "!", "*", "**", "/", "^", "^~", "~^", "~",
				"?", "<", "<<", "<=", "<<<", ">", ">>", ">=", ">>>", "=", "*=",
				"/=", "%=", "+=", "==", "!=", "-=", "<<=", ">>=", "<<<=", ">>>=",
				"&=", "^=", "|=", "===", "!==", "==?", "!=?", "--", "++", "~&", "~|", ":"}) {
			fBinaryOps.add(op);
		}
	}
}

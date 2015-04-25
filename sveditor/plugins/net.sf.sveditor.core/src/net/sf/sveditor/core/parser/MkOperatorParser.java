package net.sf.sveditor.core.parser;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class MkOperatorParser implements ISVOperators {
	private PrintStream					fPS;
	
	public MkOperatorParser(PrintStream ps) {
		fPS = ps;
	}
	
	Map<String, OP> ops_op_map = new HashMap<String, OP>();
	
	private void build() {
		List<String> ops = new ArrayList<String>();
		
		for (OP op : OP.values()) {
			if (!ops.contains(op.getImg())) {
				ops.add(op.getImg());
				ops_op_map.put(op.getImg(), op);
			} else {
				System.out.println("Duplicate op: " + op.getImg() + " " + op);
			}
		}
		
		Collections.sort(ops);
		
		String ind = "";
		
		fPS.println(ind + "class SVOperatorLexer implements ISVOperators {");
		
		ind += "  ";
		
		fPS.println(ind + "static OP operator(ITextScanner scanner) throws SVParseException {");
		fPS.println(ind + "  int ch = scanner.get_ch();");
		fPS.println(ind + "  OP op = null;");
		fPS.println();
		fPS.println(ind + "  switch (ch) {");
		
		while (ops.size() > 0) {
			String op = ops.remove(0);
			List<String> subops = new ArrayList<String>();
			
			for (int i=0; i<ops.size(); i++) {
				String so = ops.get(i);
				if (so.charAt(0) == op.charAt(0)) {
					ops.remove(i);
					i--;
					if (so.length() > 1) {
						subops.add(so);
					}
				}
			}
			
			fPS.println("// OPS: " + oplist(subops));
		
			if (op.charAt(0) == '\'') {
				fPS.println(ind + "    case '\\" + op.charAt(0) + "': {");
			} else {
				fPS.println(ind + "    case '" + op.charAt(0) + "': {");
			}
			
			if (subops.size() == 0) {
				// This is a single-character operator
				fPS.println(ind + "      op = OP." + ops_op_map.get(op) + ";");
			} else {
				// More work to do
				subcase(ind + "      ", 1, "" + op.charAt(0), subops);
			}
			fPS.println(ind + "      } break;");
		}
		fPS.println(ind + "  }");
		fPS.println(ind + "  return op;");
		fPS.println(ind + "}");
		
		fPS.println("}");
	}
	
	private void subcase(String ind, int idx, String prefix, List<String> ops) {
		String lv = "c" + idx;
		
		fPS.println(ind + "int " + lv + " = scanner.get_ch();");
//		fPS.println(ind + "switch (" + lv + ") {");
		boolean first = true;
		
		while (ops.size() > 0) {
			String op = ops.remove(0);
			if (idx >= op.length()) {
				System.out.println("idx=" + idx + " exceeds op=" + op);
			}
			char ch = op.charAt(idx);
			List<String> subops = new ArrayList<>();
			String opl = null;
		
			// Add all ops that have the next char
			for (int i=0; i<ops.size(); i++) {
				if (ops.get(i).charAt(idx) == ch) {
					String op_t = ops.remove(i);
					i--;
					if (op_t.length() > idx+1) {
						subops.add(op_t);
					} else {
						if (opl != null) {
							System.out.println("More than one localop: " + opl + " " + op_t);
						}
						opl = op_t;
					}
				}
			}
			
			if (subops.size() > 0) {
				fPS.println("// OPS: " + oplist(subops));
				if (first) {
					fPS.println(ind + "  if (" + lv + " == '" + ch + "') {");
					first = false;
				} else {
					fPS.println(ind + "  } else if (" + lv + " == '" + ch + "') {");
				}
//				fPS.println(ind + "  case '" + ch + "': {");
				subcase(ind + "    ", idx+1, prefix + ch, subops);
//				fPS.println(ind + "  } break;");
			} else {
				String full_op = prefix + ch;
				if (op.length() > full_op.length()) {
					if (first) {
						fPS.println(ind + "  if (" + lv + " == '" + ch + "') {");
						first = false;
					} else {
						fPS.println(ind + "  } else if (" + lv + " == '" + ch + "') {");
					}
//					fPS.println(ind + "  case '" + ch + "': ");
					for (int i=full_op.length(); i<op.length(); i++) {
						fPS.println(ind + "    scanner.get_ch();");
						fPS.println(ind + "    op = OP." + ops_op_map.get(op) + ";");
					}
//					fPS.println(ind + "  break;");
				} else {
					if (first) {
						fPS.println(ind + "  if (" + lv + " == '" + ch + "') {");
						first=false;
					} else {
						fPS.println(ind + "  } else if (" + lv + " == '" + ch + "') {");
					}
//					fPS.print(ind + "  case '" + ch + "': ");
					fPS.println(ind + "    op = OP." + ops_op_map.get(prefix + ch) + ";");
//					fPS.println("break;");
				}
			}
		}
		
//		fPS.println(ind + "  default: {");
		fPS.println(ind + "  } else {");
		fPS.println(ind + "    op = OP." + ops_op_map.get(prefix) + ";");
		fPS.println(ind + "    scanner.unget_ch(" + lv + ");");
		fPS.println(ind + "  }");
		
//		fPS.println(ind + "}");
	}
	
	private String oplist(List<String> ops) {
		StringBuilder sb = new StringBuilder();
		for (String op : ops) {
			sb.append(op);
			sb.append(" ");
		}
		return sb.toString();
	}
	
	public static final void main(String args[]) {
		MkOperatorParser p = new MkOperatorParser(System.out);
		p.build();
	}

	

}

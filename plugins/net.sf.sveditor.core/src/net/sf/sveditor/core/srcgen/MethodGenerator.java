package net.sf.sveditor.core.srcgen;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class MethodGenerator {
	
	public String generate(SVDBTaskFuncScope tf) {
		StringBuilder new_tf = new StringBuilder();
		
		if (tf.getType() == SVDBItemType.Function) {
			SVDBTypeInfo ti = tf.getReturnType();
			new_tf.append("    function ");
			new_tf.append(ti.toString());
			new_tf.append(" ");
		} else {
			new_tf.append("    task ");
		}
		
		new_tf.append(tf.getName());
		new_tf.append("(");
		
		for (int i=0; i<tf.getParams().size(); i++) {
			SVDBTaskFuncParam p = tf.getParams().get(i);
			SVDBTypeInfo ti = p.getTypeInfo();
			
			if ((p.getDir() & SVDBTaskFuncParam.Direction_Const) != 0) {
				new_tf.append("const ");
			}
			if ((p.getDir() & SVDBTaskFuncParam.Direction_Ref) != 0) {
				new_tf.append("ref ");
			} else if ((p.getDir() & SVDBTaskFuncParam.Direction_Var) != 0) {
				new_tf.append("var ");
			} else if ((p.getDir() & SVDBTaskFuncParam.Direction_Input) != 0) {
				new_tf.append("input ");
			} else if ((p.getDir() & SVDBTaskFuncParam.Direction_Output) != 0) {
				new_tf.append("output ");
			} else if ((p.getDir() & SVDBTaskFuncParam.Direction_Inout) != 0) {
				new_tf.append("inout ");
			}
			
			new_tf.append(ti.toString());
			new_tf.append(" ");
			new_tf.append(p.getName());
			
			if (i+1 < tf.getParams().size()) {
				new_tf.append(", ");
			}
		}
		
		new_tf.append(");\n");
		
		new_tf.append("\n");
		
		if (tf.getType() == SVDBItemType.Function) {
			new_tf.append("    endfunction\n");
		} else {
			new_tf.append("    endtask\n");
		}
		
		new_tf.append("\n");

		return new_tf.toString();
	}

}

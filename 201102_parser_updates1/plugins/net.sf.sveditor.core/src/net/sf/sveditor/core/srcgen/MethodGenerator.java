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


package net.sf.sveditor.core.srcgen;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

public class MethodGenerator {
	
	public String generate(SVDBTask tf) {
		StringBuilder new_tf = new StringBuilder();
		String classname = "";
		
		if (tf.getParent() != null && tf.getParent().getType() == SVDBItemType.ClassDecl) {
			classname = ((ISVDBNamedItem)tf.getParent()).getName();
		}
		
		new_tf.append("    /**\n" +
					  "     * " + tf.getName() + "()\n" +
					  "     *\n" +
					  "     * Override from class " + classname + "\n" +
					  "     */\n");
		
		new_tf.append("    ");
		
		if ((tf.getAttr() & SVDBFieldItem.FieldAttr_Virtual) != 0) {
			new_tf.append("virtual ");
		}
		
		if (tf.getType() == SVDBItemType.Function) {
			SVDBTypeInfo ti = ((SVDBFunction)tf).getReturnType();
			new_tf.append("function ");
			new_tf.append(ti.toString());
			new_tf.append(" ");
		} else {
			new_tf.append("task ");
		}
		
		new_tf.append(tf.getName());
		new_tf.append("(");
		
		for (int i=0; i<tf.getParams().size(); i++) {
			SVDBParamPortDecl p = tf.getParams().get(i);
			SVDBTypeInfo ti = p.getTypeInfo();
			
			if ((p.getDir() & SVDBParamPortDecl.Direction_Const) != 0) {
				new_tf.append("const ");
			}
			if ((p.getDir() & SVDBParamPortDecl.Direction_Ref) != 0) {
				new_tf.append("ref ");
			} else if ((p.getDir() & SVDBParamPortDecl.Direction_Var) != 0) {
				new_tf.append("var ");
			} else if ((p.getDir() & SVDBParamPortDecl.Direction_Input) != 0) {
				new_tf.append("input ");
			} else if ((p.getDir() & SVDBParamPortDecl.Direction_Output) != 0) {
				new_tf.append("output ");
			} else if ((p.getDir() & SVDBParamPortDecl.Direction_Inout) != 0) {
				new_tf.append("inout ");
			}
			
			new_tf.append(ti.toString());
			new_tf.append(" ");
			for (SVDBVarDeclItem vi : p.getVarList()) {
				new_tf.append(vi.getName());
				
				new_tf.append(", ");
			}
		}
		new_tf.setLength(new_tf.length()-2);
		
		if (new_tf.toString().endsWith(", ")) {
			new_tf.setLength(new_tf.length()-2);
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

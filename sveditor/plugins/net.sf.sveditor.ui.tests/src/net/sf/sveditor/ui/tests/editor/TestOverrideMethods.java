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


package net.sf.sveditor.ui.tests.editor;

import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfoClassItem;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;
import net.sf.sveditor.core.srcgen.OverrideMethodsFinder;
import net.sf.sveditor.core.tests.TextTagPosUtils;
import net.sf.sveditor.core.tests.indent.IndentComparator;
import net.sf.sveditor.ui.editor.actions.IOverrideMethodsTargetProvider;
import net.sf.sveditor.ui.editor.actions.OverrideTaskFuncImpl;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;

public class TestOverrideMethods extends TestCase {
	
	public void testOverrideFunction() throws BadLocationException {
		String doc = 
			"class base;\n" +
			"\n" +
			"	function void my_func();\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class extension extends base;\n" +
			"    <<MARK>>\n" +
			"endclass\n" +
			"\n"
			;
		
		String expected = 
			"class base;\n" +
			"\n" +
			"	function void my_func();\n" +
		    "	endfunction\n" +
		    "endclass\n" +
		    "\n" +
		    "class extension extends base;\n" +
		    "\n" +
		    "\n" +
		    "	/**\n" +
		    "	 * Function: my_func\n" +
		    "	 *\n" +
		    "	 * Override from class base\n" +
		    "	 */\n" +
		    "	function void my_func();\n" +
		    "	\n" +
		    "	endfunction\n" +
		    "\n" +
		    "\n" +
		    "endclass\n"
		    ;
		
		core_testOverrideAll("testOverrideFunction", doc, expected, "extension");
	}

	public void testVirtualFunction() throws BadLocationException {
		String doc = 
			"virtual class base;\n" +
			"\n" +
			"	virtual function void my_func();\n" +
			"	endfunction : my_func\n" +
			"endclass\n" +
			"\n" +
			"class extension extends base;\n" +
			"    <<MARK>>\n" +
			"endclass\n" +
			"\n"
			;
		
		String expected = 
			"virtual class base;\n" +
			"\n" +
			"	virtual function void my_func();\n" +
		    "	endfunction : my_func\n" +
		    "endclass\n" +
		    "\n" +
		    "class extension extends base;\n" +
		    "\n" +
		    "\n" +
		    "	/**\n" +
		    "	 * Function: my_func\n" +
		    "	 *\n" +
		    "	 * Override from class base\n" +
		    "	 */\n" +
		    "	virtual function void my_func();\n" +
		    "	\n" +
		    "	endfunction\n" +
		    "\n" +
		    "\n" +
		    "endclass\n"
		    ;
		
		core_testOverrideAll("testVirtualFunction", doc, expected, "extension");
	}
	
	public void testOverrideRefArgTask() throws BadLocationException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"virtual class base;\n" +
			"\n" +
			"	virtual task my_func(ref int a);\n" +
			"	endtask : my_func\n" +
			"endclass\n" +
			"\n" +
			"class extension extends base;\n" +
			"    <<MARK>>\n" +
			"endclass\n" +
			"\n"
			;
		
		String expected = 
			"virtual class base;\n" +
			"\n" +
			"	virtual task my_func(ref int a);\n" +
			"	endtask : my_func\n" +
		    "endclass\n" +
		    "\n" +
		    "class extension extends base;\n" +
		    "\n" +
		    "\n" +
		    "	/**\n" +
		    "	 * Task: my_func\n" +
		    "	 *\n" +
		    "	 * Override from class base\n" +
		    "	 */\n" +
			"	virtual task my_func(ref int a);\n" +
			"	\n" +
			"	endtask\n" +
		    "\n" +
		    "\n" +
		    "endclass\n"
		    ;
		
		core_testOverrideAll("testOverrideRefArgTask", doc, expected, "extension");
	}

	public void testOverrideInOutTask() throws BadLocationException {
		String doc = 
			"virtual class base;\n" +
			"\n" +
			"	virtual task my_func(input int a, output int b);\n" +
			"	endtask : my_func\n" +
			"endclass\n" +
			"\n" +
			"class extension extends base;\n" +
			"    <<MARK>>\n" +
			"endclass\n" +
			"\n"
			;
		
		String expected = 
			"virtual class base;\n" +
			"\n" +
			"	virtual task my_func(input int a, output int b);\n" +
			"	endtask : my_func\n" +
		    "endclass\n" +
		    "\n" +
		    "class extension extends base;\n" +
		    "\n" +
		    "\n" +
		    "	/**\n" +
		    "	 * Task: my_func\n" +
		    "	 *\n" +
		    "	 * Override from class base\n" +
		    "	 */\n" +
			"	virtual task my_func(input int a, output int b);\n" +
			"	\n" +
			"	endtask\n" +
		    "\n" +
		    "\n" +
		    "endclass\n"
		    ;
		
		core_testOverrideAll("testOverrideRefArgTask", doc, expected, "extension");
	}


	public void core_testOverrideAll(
			String				test_name,
			String 				doc,
			String				expected,
			String				extension_class_name) throws BadLocationException {
		TextTagPosUtils tag_utils = new TextTagPosUtils(doc);
		
		
		SVEditorTester sve_tester = new SVEditorTester(
				tag_utils.getStrippedData(), "testOverrideFunction");

		ITextSelection sel = new TextSelection(
				sve_tester.getDocument(), tag_utils.getTagPos("MARK"), 1);
		sve_tester.getAutoEdit().setCaretOffset(tag_utils.getTagPos("MARK"));
		sve_tester.setSelection(sel);
		
		SVDBClassDecl extension = null;
		SVDBClassDecl	base = null;
		for (ISVDBItemBase it : sve_tester.getSVDBFile().getChildren()) {
			if (SVDBItem.getName(it).equals(extension_class_name)) {
				extension = (SVDBClassDecl)it;
			}
		}
		assertNotNull(extension);

		SVDBTypeInfoClassType ci = extension.getSuperClass();
		for (ISVDBItemBase it : sve_tester.getSVDBFile().getChildren()) {
			System.out.println("extension=" + ci.getName() + " it=" + SVDBItem.getName(it));
			if (SVDBItem.getName(it).equals(ci.getName())) {
				base = (SVDBClassDecl)it;
			}
		}
		assertNotNull(base);
		
		OverrideMethodsFinder finder = new OverrideMethodsFinder(
				extension, sve_tester.getIndexIterator());
		final List<SVDBTask> targets = finder.getMethods(base);
		
		OverrideTaskFuncImpl override = new OverrideTaskFuncImpl(
				sve_tester, new IOverrideMethodsTargetProvider() {
					
					@Override
					public List<SVDBTask> getTargets(ISVDBScopeItem activeScope) {
						return targets;
					}
				});
		
		override.run();
		
		String result = sve_tester.getDocument().get();
		
		IndentComparator.compare(test_name, expected, result);
	}

}

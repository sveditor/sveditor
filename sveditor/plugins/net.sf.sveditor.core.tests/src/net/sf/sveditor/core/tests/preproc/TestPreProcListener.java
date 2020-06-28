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
package net.sf.sveditor.core.tests.preproc;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.db.SVDBMacroDef;
import org.eclipse.hdt.sveditor.core.db.SVDBMacroDefParam;
import org.eclipse.hdt.sveditor.core.preproc.IPreProcListener;
import org.eclipse.hdt.sveditor.core.preproc.PreProcEvent;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcOutput;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcessor;
import org.eclipse.hdt.sveditor.core.preproc.SVStringPreProcessor;
import org.eclipse.hdt.sveditor.core.preproc.PreProcEvent.Type;
import org.eclipse.hdt.sveditor.core.scanner.SVPreProcDefineProvider;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestPreProcListener extends SVCoreTestCaseBase implements IPreProcListener {
	private List<PreProcEvent>	fEvents = new ArrayList<PreProcEvent>();
	
	
	@Override
	public void preproc_event(PreProcEvent event) {
		fLog.debug("preproc_event: " + event.type + " " + event.text + " " + event.pos);
		fEvents.add(event);
	}

	public void testListener1() {
		String doc = 
			"`define MY_MACRO(A1, A2) \\\n" +
			"	class A1;\\\n" +
			"		int A2;\\\n" +
			"	endclass\n" +
			"\n" +
			"`MY_MACRO(foo, bar)\n"
			;
		
		runExpandEventsTest(doc, null, 
				new String[] {
						"class foo;\n" +
						"	int bar;\n" +
						"endclass\n"
				});
	}
	
	public void testNestedMacroListener() {
		SVCorePlugin.getDefault().enableDebug(false);

		List<SVDBMacroDefParam> params;
		
		SVDBMacroDef my_field = new SVDBMacroDef("MY_FIELD", "int A1");
		params = new ArrayList<SVDBMacroDefParam>();
		params.add(new SVDBMacroDefParam("A1", ""));
		my_field.setParameters(params);
		
		SVDBMacroDef my_macro = new SVDBMacroDef("MY_MACRO", 
				"class A1;\n" +
				"	`MY_FIELD(A2);\n" +
				"endclass\n");
		params = new ArrayList<SVDBMacroDefParam>();
		params.add(new SVDBMacroDefParam("A1", ""));
		params.add(new SVDBMacroDefParam("A2", ""));
		my_macro.setParameters(params);
		
		String doc = "`MY_MACRO(foo, bar)\n";
		
		runExpandEventsTest(doc, 
				new SVDBMacroDef[] {
					my_field,
					my_macro
				}, 
				new String[] {
					"int bar",
					"class foo;\n" +
					"	int bar;\n" +
					"endclass\n"
				});
	}
	
	private void runExpandEventsTest(
			String				doc,
			SVDBMacroDef		macros[],
			String				exp[]
			) {
		SVPreProcessor preproc = new SVPreProcessor(
				getName(), new StringInputStream(doc), null, null);
		fEvents.clear();
	
		if (macros != null) {
			for (SVDBMacroDef m : macros) {
				preproc.addMacro(m);
			}
		}
		
		preproc.addListener(this);
		
		String result = preproc.preprocess().toString();
		
		fLog.debug("Result:\n" + result);
		
		Stack<PreProcEvent>	stack = new Stack<PreProcEvent>();
		List<String> results = new ArrayList<String>();
		
		for (PreProcEvent e : fEvents) {
			if (e.type == Type.BeginExpand) {
				stack.push(e);
			} else if (e.type == Type.EndExpand) {
				PreProcEvent be = stack.pop();
				results.add(result.substring(be.pos, e.pos));
			}
		}
		
		for (String r : results) {
			r = TestPreProc2.trimLines(r);
			fLog.debug("Result: \"" + r + "\"");
		}
		
		assertEquals(exp.length, results.size());
		
		for (int i=0; i<exp.length; i++) {
			String r = TestPreProc2.trimLines(results.get(i));
			String e = TestPreProc2.trimLines(exp[i]);
			assertEquals(e, r);
		}
	}

}

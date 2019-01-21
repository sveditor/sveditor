package net.sf.sveditor.core.tests.preproc;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.preproc.ISVPreProcListener;
import net.sf.sveditor.core.preproc.SVPreProcEvent;
import net.sf.sveditor.core.preproc.SVPreProcEvent.Type;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestPreProcListener extends SVCoreTestCaseBase 
	implements ISVPreProcListener {
	private List<SVPreProcEvent>	fEvents = new ArrayList<SVPreProcEvent>();
	

	@Override
	public void preproc_event(SVPreProcEvent event) {
		// TODO Auto-generated method stub
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
		
		Stack<SVPreProcEvent>	stack = new Stack<SVPreProcEvent>();
		List<String> results = new ArrayList<String>();
		
		for (SVPreProcEvent e : fEvents) {
			if (e.type == Type.BeginExpand) {
				stack.push(e);
			} else if (e.type == Type.EndExpand) {
				SVPreProcEvent be = stack.pop();
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

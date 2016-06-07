package net.sf.sveditor.core.tests.preproc;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.preproc.IPreProcListener;
import net.sf.sveditor.core.preproc.PreProcEvent;
import net.sf.sveditor.core.preproc.PreProcEvent.Type;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.preproc.SVStringPreProcessor;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestPreProcListener extends SVCoreTestCaseBase implements IPreProcListener {
	private List<PreProcEvent>	fEvents = new ArrayList<PreProcEvent>();
	
	
	@Override
	public void preproc_event(PreProcEvent event) {
		System.out.println("preproc_event: " + event.type + " " + event.text + " " + event.pos);
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
		
		SVPreProcessor2 preproc = new SVPreProcessor2(getName(), 
				new StringInputStream(doc), null, null);
	//	preproc.addPreProcListener(this);
		
		SVPreProcOutput out = preproc.preprocess();
		System.out.println("Result:\n" + out.toString());
		
	}
	
	public void testNestedMacroListener() {
		SVCorePlugin.getDefault().enableDebug(false);
		SVStringPreProcessor preproc = new SVStringPreProcessor();
//		preproc.setLocked(false);

		List<SVDBMacroDefParam> params = new ArrayList<SVDBMacroDefParam>();
		SVDBMacroDef m = new SVDBMacroDef("MY_FIELD", "int A1");
		params.clear();
		params.add(new SVDBMacroDefParam("A1", ""));
		m.setParameters(params);
		preproc.addMacro(m);
		
		m = new SVDBMacroDef("MY_MACRO", 
				"class A1;\n" +
				"	`MY_FIELD(A2);\n" +
				"endclass\n");
		params.clear();
		params.add(new SVDBMacroDefParam("A1", ""));
		params.add(new SVDBMacroDefParam("A2", ""));
		m.setParameters(params);
		preproc.addMacro(m);
		
		String doc = "`MY_MACRO(foo, bar)\n";

		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(preproc);
		dp.addPreProcListener(this);
		
		String result = dp.expandMacro(doc, getName(), 1);
		
		System.out.println("Macro subset(1):\n" +
				result.substring(fEvents.get(1).pos, fEvents.get(2).pos));
		
		System.out.println("Macro subset(2):\n" +
				result.substring(fEvents.get(0).pos, fEvents.get(3).pos));
	
		Stack<PreProcEvent>	stack = new Stack<PreProcEvent>();
		
		for (PreProcEvent e : fEvents) {
			if (e.type == Type.BeginExpand) {
				stack.push(e);
			} else if (e.type == Type.EndExpand) {
				PreProcEvent be = stack.pop();
				System.out.println("Scope: " + be.text + "\n" +
						result.substring(be.pos, e.pos));
			} else {
				System.out.println("Unknown event: " + e.type);
			}
		}
		// Keep pushing until 
		
		
		System.out.println("Result:\n" + result);
	}	

}

package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistPriority extends SVCoreTestCaseBase {
	
	public void testUntriggeredClassHierarchy() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class cls1;\n" +
			"  int			m_def;\n" +
			"  int			m_abc;\n" +
			"endclass\n" +
			"\n" +
			"class cls2 extends cls1;\n" +
			"  int			m_jkl;\n" +
			"  int			m_ghi;\n" +
			"endclass\n" +
			"\n" +
			"class cls3 extends cls2;\n" +
			"  int			m_pqr;\n" +
			"  int			m_mno;\n" +
			"\n" +
			"  function void foo;\n" +
			"    m_<<MARK>>\n" +
			"  endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(
				this, doc, false, true,
				"m_mno",
				"m_pqr",
				"m_ghi",
				"m_jkl",
				"m_abc",
				"m_def"
				);		
	}
	
	public void testTriggeredClassHierarchy() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class cls1;\n" +
			"  int			m_def;\n" +
			"  int			m_abc;\n" +
			"endclass\n" +
			"\n" +
			"class cls2 extends cls1;\n" +
			"  int			m_jkl;\n" +
			"  int			m_ghi;\n" +
			"endclass\n" +
			"\n" +
			"class cls3 extends cls2;\n" +
			"  int			m_pqr;\n" +
			"  int			m_mno;\n" +
			"\n" +
			"  function void foo;\n" +
			"    cls3 c;\n" +
			"    c.m_<<MARK>>\n" +
			"  endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(
				this, doc, false, true,
				"m_mno",
				"m_pqr",
				"m_ghi",
				"m_jkl",
				"m_abc",
				"m_def"
				);
	}

	public void testLocalScopeVars() {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"class cls1;\n" +					// 1
			"  int			m_def;\n" +
			"  int			m_abc;\n" +
			"endclass\n" +
			"\n" +								// 5
			"class cls2 extends cls1;\n" +
			"  int			m_jkl;\n" +
			"  int			m_ghi;\n" +
			"endclass\n" +
			"\n" +								// 10
			"class cls3 extends cls2;\n" +
			"  int			m_pqr;\n" +
			"  int			m_mno;\n" +
			"\n" +
			"  function void foo;\n" +			// 15
			"    int m_pqr;\n" +
			"    begin\n" +
			"      int m_stu;\n" +
			"		\n" +
			"      m_<<MARK>>\n" +				// 20
			"    end\n" +
			"  endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(
				this,
				doc,
				false,
				true,
				"m_stu",
				"m_pqr",
				"m_mno",
				"m_ghi",
				"m_jkl",
				"m_abc",
				"m_def"
				);		
	}
	
	public void testFieldClassOrdering() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class m_cls2;\n" +
			"endclass\n" +
			"\n" +
			"class m_cls1;\n" +
			"endclass\n" +
			"\n" +
			"class cls1;\n" +
			"  int			m_def;\n" +
			"  int			m_abc;\n" +
			"endclass\n" +
			"\n" +
			"class cls2 extends cls1;\n" +
			"  int			m_jkl;\n" +
			"  int			m_ghi;\n" +
			"endclass\n" +
			"\n" +
			"class cls3 extends cls2;\n" +
			"  int			m_pqr;\n" +
			"  int			m_mno;\n" +
			"\n" +
			"  function void foo;\n" +
			"    int m_pqr;\n" +
			"    m_<<MARK>>\n" +
			"  endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(
				this, doc, false, true,
				"m_pqr",
				"m_mno",
				"m_ghi",
				"m_jkl",
				"m_abc",
				"m_def",
				"m_cls1",
				"m_cls2"
				);		
	}	
}

package net.sf.sveditor.core.tests.searchutils;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestFindItem extends SVCoreTestCaseBase {
	
	public void testSelectInModuleInstantiation() {
		String content =
			"module top;\n" +
			"\n" +
			"\n" +
			"	subm u_sub (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 6
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(
				fLog, content, getName(), false);
	
		SVCorePlugin.getDefault().enableDebug(true);
		ISVDBItemBase it = SVDBSearchUtils.findActiveStructItem(file, 6);
	
		System.out.println("it=" + it);
		assertNotNull(it);
		assertTrue("it not instanceof SVDBModIfInst: " + it, 
				(it instanceof SVDBModIfcInstItem));
	}

	public void testSelectInModuleInstantiation_2() {
		String content =
			"module top;\n" +
			"\n" +
			"\n" +
			"	subm u_sub_1 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 6
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"	subm u_sub_2 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 12
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"	subm u_sub_3 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 18
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(
				fLog, content, getName(), false);
	
		SVCorePlugin.getDefault().enableDebug(true);
		ISVDBItemBase it = SVDBSearchUtils.findActiveStructItem(file, 12);
	
		assertNotNull(it);
		System.out.println("it=" + it + " line=" + it.getLocation().getLine());
		assertTrue("it not instanceof SVDBModIfInst: " + it, 
				(it instanceof SVDBModIfcInstItem));
		assertEquals("u_sub_2", SVDBItem.getName(it));
	}
	
	public void testSelectInModuleInstantiation_3() {
		String content =
			"module top;\n" +
			"\n" +
			"\n" +
			"	subm u_sub_1 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 6
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"	subm u_sub_2 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 12
			"		.c(a)\n" +
			"	), u_sub_2_1 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" +	// 16
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"	subm u_sub_3 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 22
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(
				fLog, content, getName(), false);
	
		SVCorePlugin.getDefault().enableDebug(true);
		ISVDBItemBase it = SVDBSearchUtils.findActiveStructItem(file, 12);
	
		assertNotNull(it);
		System.out.println("it=" + it + " line=" + it.getLocation().getLine());
		assertTrue("it not instanceof SVDBModIfInst: " + it, 
				(it instanceof SVDBModIfcInstItem));
		assertEquals("u_sub_2", SVDBItem.getName(it));
	}	

	public void testSelectInModuleInstantiation_4() {
		String content =
			"module top;\n" +
			"\n" +
			"\n" +
			"	subm u_sub_1 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 6
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"	subm u_sub_2 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 12
			"		.c(a)\n" +
			"	), u_sub_2_1 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" +	// 16 <==
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"	subm u_sub_3 (\n" +
			"		.a(a),\n" +
			"		.b(a),\n" + // 22
			"		.c(a)\n" +
			"	);\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(
				fLog, content, getName(), false);
	
		SVCorePlugin.getDefault().enableDebug(true);
		ISVDBItemBase it = SVDBSearchUtils.findActiveStructItem(file, 16);
	
		assertNotNull(it);
		System.out.println("it=" + it + " line=" + it.getLocation().getLine());
		assertTrue("it not instanceof SVDBModIfInst: " + it, 
				(it instanceof SVDBModIfcInstItem));
		assertEquals("u_sub_2_1", SVDBItem.getName(it));
	}
	
	public void testSelectInModuleInstantiation_5() {
		String content =
			"\n" +
			"module foobar;\n" +
			"\n" +
			"\n" +
			"	submodule a (\n" + // 5
			"		.b(1),\n" +
			"		.b(2),\n" +
			"		.b(3),\n" +    // 8 <==
			"		.b(4),\n" +
			"), b (\n" +
			"		.b(2)\n" +     // 11
			");\n" +
			"\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(
				fLog, content, getName(), false);
	
		SVCorePlugin.getDefault().enableDebug(true);
		ISVDBItemBase it = SVDBSearchUtils.findActiveStructItem(file, 8);
	
		assertNotNull(it);
		System.out.println("it=" + it + " line=" + it.getLocation().getLine());
		assertTrue("it not instanceof SVDBModIfInst: " + it, 
				(it instanceof SVDBModIfcInstItem));
		assertEquals("a", SVDBItem.getName(it));
	}	
}

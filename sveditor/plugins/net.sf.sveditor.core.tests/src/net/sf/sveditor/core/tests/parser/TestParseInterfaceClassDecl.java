package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;

public class TestParseInterfaceClassDecl extends TestCase {
	
	public void testInterfaceClassDecl() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"interface class test_class_interface;\n" +
			"	// provide prototype for signal change so that pve_sequencer can call it\n" +
			"	pure virtual task method_to_be_added(uvm_component sender, uvm_object data_container);\n" +
			"endclass \n" +
			"\n" +
			"class pve_predictor#(type SEQHTYPE = pve_virtual_sequencer) extends uvm_component implements test_class_interface;\n" +
			"	//blablabla\n" +
			"endclass\n" +
			"\n"
			;
		
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"test_class_interface", "pve_predictor"}
		);
	}

	public void testInterfaceClassMultiImplements() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"interface class A_ifc;\n" +
			"endclass \n" +
			"\n" +
			"interface class B_ifc;\n" +
			"endclass \n" +
			"\n" +
			"class cls implements A_ifc, B_ifc;\n" +
			"endclass\n" +
			"\n"
			;
		
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"cls"}
		);
	}
	
	public void testInterfaceClassMultiExtends() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"interface class A_ifc;\n" +
			"endclass \n" +
			"\n" +
			"interface class B_ifc;\n" +
			"endclass \n" +
			"\n" +
			"interface class C_ifc extends A_ifc, B_ifc;\n" +
			"endclass\n" +
			"\n"
			;
		
		ParserTests.runTestStrDoc(getName(), doc, 
				new String[] {"A_ifc", "B_ifc", "C_ifc"}
		);
	}	
}

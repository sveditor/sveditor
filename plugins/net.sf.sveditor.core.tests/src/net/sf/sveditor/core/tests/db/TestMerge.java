package net.sf.sveditor.core.tests.db;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.parser.ParserTests;
import junit.framework.TestCase;

public class TestMerge extends TestCase {
	
	public void testMergeNewField() {
		String orig_file_content = 
			"class c;\n" +
			"    int field1;\n" +
			"endclass\n"
			;
		String new_file_content =
			"class c;\n" +
			"    int field1;\n" +
			"    int field2;\n" +
			"endclass\n"
			;
		
		SVDBFile orig_file = SVDBTestUtils.parse(orig_file_content, "file.svh");
		SVDBFile new_file = SVDBTestUtils.parse(new_file_content, "file.svh");
		
		SVDBTestUtils.assertNoErrWarn(orig_file);
		SVDBTestUtils.assertNoErrWarn(new_file);
		
		SVDBTestUtils.assertFileHasElements(orig_file, "field1");
		SVDBTestUtils.assertFileHasElements(new_file, "field1", "field2");
		
		assertFalse(orig_file.equals(new_file));
		
		SVDBFileMerger.merge(orig_file, new_file, null, null, null);
		
		SVDBTestUtils.assertFileHasElements(orig_file, "field1", "field2");
	}

}

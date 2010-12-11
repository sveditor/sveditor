package net.sf.sveditor.core.tests.open_decl;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestOpenClass extends TestCase {
	
	
	public void testOpenScopedClassReference() {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"package foo;\n" +
			"	class foo_c;\n" +
			"	endclass\n" +
			"endpackage\n" +
			"\n" +
			"\n" +
			"module bar;\n" +
			"	foo::foo_c		item;\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenScopedClassReference.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("foo::foo_c");
		System.out.println("index: " + idx);
		scanner.seek(idx+"foo::fo".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<SVDBItem, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 4, scanner, target_index);
		
		System.out.println(ret.size() + " items");
		assertEquals(1, ret.size());
	}

}

package net.sf.sveditor.core.tests.parser;

import java.io.ByteArrayOutputStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;

public class TestSystemParse extends TestCase {
	
	public void testParseOvmSequenceUtils() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		ByteArrayOutputStream bos = utils.readBundleFile("/data/ovm_sequence_utils.svh");
		
		SVDBFile file = SVDBTestUtils.parse(bos.toString(), "ovm_sequence_utils.svh");
		SVDBTestUtils.assertNoErrWarn(file);
	}
}

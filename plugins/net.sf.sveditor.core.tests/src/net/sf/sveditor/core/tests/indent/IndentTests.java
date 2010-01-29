package net.sf.sveditor.core.tests.indent;

import java.io.ByteArrayOutputStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.indent.SVDefaultIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.utils.BundleUtils;

public class IndentTests extends TestCase {
	
	public void testBasics() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		ByteArrayOutputStream bos;
		
		bos = utils.readBundleFile("/data/basic_content_assist_project/class1.svh");
		
		SVIndentScanner scanner = new SVIndentScanner(new SVDefaultIndenter());
		
		StringBuilder sb = new StringBuilder(bos.toString());
		String result = scanner.indent(new StringTextScanner(sb), 20, 150);
		
		System.out.println("Result: \"" + result + "\"");
	}

}

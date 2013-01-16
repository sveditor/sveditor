package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestBasicParsing extends SVCoreTestCaseBase {

	public void testParseUVM() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().setTestDebugLevel(2);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		TestUtils.copy(
				"+incdir+uvm/src\n" +
				"uvm/src/uvm_pkg.sv",
				new File(fTmpDir, "uvm.f"));
		
		String base_location = new File(fTmpDir, "uvm.f").getAbsolutePath();
		
		SVDBArgFileIndex2 index = new SVDBArgFileIndex2(
				getName(), base_location,
				new SVDBWSFileSystemProvider(),
				fCacheFactory.createIndexCache(getName(), base_location),
				null);
		
		long start, end;
		
		start = System.currentTimeMillis();
		index.init(new NullProgressMonitor());
		index.loadIndex(new NullProgressMonitor());
		end = System.currentTimeMillis();
		
		System.out.println("Parse UVM in " + (end-start) + "ms");

	}
	
	public void testParseUVM_old() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().setTestDebugLevel(0);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		TestUtils.copy(
				"+incdir+uvm/src\n" +
				"uvm/src/uvm_pkg.sv",
				new File(fTmpDir, "uvm.f"));
		
		String base_location = new File(fTmpDir, "uvm.f").getAbsolutePath();
		
		SVDBArgFileIndex index = new SVDBArgFileIndex(
				getName(), base_location,
				new SVDBWSFileSystemProvider(),
				fCacheFactory.createIndexCache(getName(), base_location),
				null);
	
		long start, end;
		
		start = System.currentTimeMillis();
		index.init(new NullProgressMonitor());
		index.loadIndex(new NullProgressMonitor());
		end = System.currentTimeMillis();
		
		System.out.println("Parse UVM in " + (end-start) + "ms");
	}	
}

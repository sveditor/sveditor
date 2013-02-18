package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
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
		
		for (String path : index.getFileList(new NullProgressMonitor())) {
			System.out.println("Path: " + path);
			start = System.currentTimeMillis();
			SVDBFile file = index.findFile(path);
			end = System.currentTimeMillis();
			System.out.println("Extract " + path + " " + (end-start) + "ms");
			assertNotNull("Failed to find file " + path, file);
		}
		
	
		/*
		SVDBFile uvm_component_svh = index.findFile(
				new File(fTmpDir, "uvm/src/base/uvm_component.svh").getAbsolutePath());
		print("", uvm_component_svh);
		SVDBFile uvm_pkg_sv = index.findFile(
				new File(fTmpDir, "uvm/src/uvm_pkg.sv").getAbsolutePath());
		print("", uvm_pkg_sv);
		 */

	}
	
	private void print(String ind, ISVDBChildParent parent) {
		System.out.println(ind + parent.getType() + " " + SVDBItem.getName(parent));
	
		ind += "  ";
		for (ISVDBChildItem c : parent.getChildren()) {
			if (c instanceof ISVDBChildParent) {
				print(ind, (ISVDBChildParent)c);
			} else {
				System.out.println(ind + c.getType() + " " + SVDBItem.getName(parent));
			}
		}
	}

	public void testParseUltraSPARC() {
		SVCorePlugin.getDefault().setTestDebugLevel(2);
	
		String base_location = "/home/ballance.2/Downloads/OpenSPARCT2/design/design.f";
		
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
		
		for (String path : index.getFileList(new NullProgressMonitor())) {
			System.out.println("Path: " + path);
			start = System.currentTimeMillis();
			SVDBFile file = index.findFile(path);
			end = System.currentTimeMillis();
			System.out.println("Extract " + path + " " + (end-start) + "ms");
			assertNotNull("Failed to find file " + path, file);
		}
		
	
		/*
		SVDBFile uvm_component_svh = index.findFile(
				new File(fTmpDir, "uvm/src/base/uvm_component.svh").getAbsolutePath());
		print("", uvm_component_svh);
		SVDBFile uvm_pkg_sv = index.findFile(
				new File(fTmpDir, "uvm/src/uvm_pkg.sv").getAbsolutePath());
		print("", uvm_pkg_sv);
		 */

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

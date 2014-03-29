package net.sf.sveditor.core.tests.index.refs;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.ops.SVDBFindClassExtensionsOp;
import net.sf.sveditor.core.db.refs.SVDBFindReferencesOp;
import net.sf.sveditor.core.db.refs.SVDBRefCollectorVisitor;
import net.sf.sveditor.core.db.refs.SVDBRefSearchSpecClassFieldRefsByName;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestClassRefs extends SVCoreTestCaseBase {

	public void disabled_testFindUVMComponentGetParent() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, getName());
		
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/uvm.zip",  test_dir);
		File uvm = new File(test_dir, "uvm");
		TestUtils.copy(
				"+incdir+./src\n" +
				"./src/uvm_pkg.sv\n",
				new File(uvm, "uvm.f"));
		
		IProject project = TestUtils.createProject("uvm", uvm);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"GLOBAL", "${workspace_loc}/uvm/uvm.f",
				SVDBArgFileIndexFactory.TYPE, null);
	
		index.loadIndex(new NullProgressMonitor());

		SVDBFindByName finder = new SVDBFindByName(index, 
				new SVDBFindByNameMatcher(SVDBItemType.ClassDecl));
		List<SVDBDeclCacheItem> items = finder.find("uvm_component", true, SVDBItemType.ClassDecl);
		
		assertEquals(1, items.size());
		ISVDBChildItem get_parent = findClassField(
				(SVDBClassDecl)items.get(0).getSVDBItem(), "get_parent");

		assertNotNull(get_parent);
		SVDBRefSearchSpecClassFieldRefsByName ref_spec = 
				new SVDBRefSearchSpecClassFieldRefsByName(index, get_parent);
		
		SVDBRefCollectorVisitor visitor = new SVDBRefCollectorVisitor();
	
		index.execOp(new NullProgressMonitor(), 
				new SVDBFindReferencesOp(ref_spec, visitor), true);
		
		assertEquals(1, visitor.getItemList().size());
		/*
		 */
		
	}

	public void testFindUVMComponentExtensions() {
		SVCorePlugin.getDefault().enableDebug(false);
		SVCorePlugin.getDefault().setDebugLevel(LEVEL_MIN);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, getName());
		
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/uvm.zip",  test_dir);
		File uvm = new File(test_dir, "uvm");
		TestUtils.copy(
				"+incdir+./src\n" +
				"./src/uvm_pkg.sv\n",
				new File(uvm, "uvm.f"));
		
		IProject project = TestUtils.createProject("uvm", uvm);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"GLOBAL", "${workspace_loc}/uvm/uvm.f",
				SVDBArgFileIndexFactory.TYPE, null);
	
		index.loadIndex(new NullProgressMonitor());

		SVDBFindByName finder = new SVDBFindByName(index, 
				new SVDBFindByNameMatcher(SVDBItemType.ClassDecl));
		List<SVDBDeclCacheItem> items = finder.find("uvm_component", true, SVDBItemType.ClassDecl);
		
		assertEquals(1, items.size());
	
		long start = System.currentTimeMillis();
		List<SVDBDeclCacheItem> extensions = SVDBFindClassExtensionsOp.execOp(
				new NullProgressMonitor(), 
				index, (SVDBClassDecl)items.get(0).getSVDBItem());
		long end = System.currentTimeMillis();
		
		fLog.debug(LEVEL_MIN, "Extension finding time: " + (end-start));
		
		assertEquals(17, extensions.size());
	}
	
	public void disabled_testFindDirectFieldMethodRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		File test_dir = new File(fTmpDir, getName());
		
		assertTrue(test_dir.mkdirs());
		
		TestUtils.copy(
				"class cls1;\n" +
				"	task foo;\n" +
				"	endtask\n" +
				"	task bar;\n" +
				"		foo();\n" +
				"	endtask\n" +
				"endclass\n",
				new File(test_dir, "cls1.svh"));
		
		TestUtils.copy(
				"class cls2;\n" +
				"	cls1		f1;\n" +
				"	task bar;\n" +
				"		f1.foo();\n" +
				"	endtask\n" +
				"endclass\n",
				new File(test_dir, "cls2.svh"));
		
		TestUtils.copy(
				"package pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"	`include \"cls2.svh\"\n" +
				"endpackage\n",
				new File(test_dir, "pkg.sv"));
		
		TestUtils.copy(
				"+incdir+./\n" +
				"pkg.sv\n",
				new File(test_dir, "test.f"));
		
		IProject project = TestUtils.createProject("test", test_dir);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"GLOBAL", "${workspace_loc}/test/test.f",
				SVDBArgFileIndexFactory.TYPE, null);
	
		index.loadIndex(new NullProgressMonitor());

		SVDBFindByName finder = new SVDBFindByName(index, 
				new SVDBFindByNameMatcher(SVDBItemType.ClassDecl));
		List<SVDBDeclCacheItem> items = finder.find("cls1", true, SVDBItemType.ClassDecl);
		
		assertEquals(1, items.size());
		
		assertEquals("cls1", SVDBItem.getName(items.get(0).getSVDBItem()));
		ISVDBChildItem foo = findClassField(
				(SVDBClassDecl)items.get(0).getSVDBItem(), "foo");

		assertNotNull(foo);
		assertEquals("foo", SVDBItem.getName(foo));
		
		SVDBRefSearchSpecClassFieldRefsByName ref_spec = 
				new SVDBRefSearchSpecClassFieldRefsByName(index,foo);
		
		SVDBRefCollectorVisitor visitor = new SVDBRefCollectorVisitor();

		System.out.println("FIND:");
		index.execOp(new NullProgressMonitor(), 
				new SVDBFindReferencesOp(ref_spec, visitor), true);
		
		assertEquals(1, visitor.getItemList().size());
		/*
		 */
		
	}
	
	private ISVDBChildItem findClassField(SVDBClassDecl cls, String name) {
		for (ISVDBChildItem item : cls.getChildren()) {
			if (name.equals(SVDBItem.getName(item))) {
				return item;
			}
		}
		
		return null;
	}
}

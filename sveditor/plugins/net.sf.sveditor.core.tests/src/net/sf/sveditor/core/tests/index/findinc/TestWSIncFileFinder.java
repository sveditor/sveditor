package net.sf.sveditor.core.tests.index.findinc;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFindIncFileUtils;
import net.sf.sveditor.core.db.index.SVDBIncFileInfo;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestWSIncFileFinder extends SVCoreTestCaseBase {
	
	public void testFindImmediateLeafFiles() {
		File pdir = new File(fTmpDir, "project");
		IProject p = TestUtils.createProject("project", pdir);
		addProject(p);
	
		String argfile = "${workspace_loc}/project/sve.f";
		SVFileUtils.copy(
				"root_pkg.sv",
				p.getFile("sve.f"));
		
		SVFileUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				p.getFile("cls1.svh"));
		
		SVFileUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				p.getFile("cls2.svh"));
		
		SVFileUtils.copy(
				"class my_cls1;\n" +
				"endclass\n",
				p.getFile("my_cls1.svh"));

		runTest(p, argfile, "cl", 
				new String[] {"cls1.svh", "cls2.svh"});
	}

	public void testFindSubDirFiles() {
		File pdir = new File(fTmpDir, "project");
		IProject p = TestUtils.createProject("project", pdir);
		addProject(p);
	
		String argfile = "${workspace_loc}/project/sve.f";
		SVFileUtils.copy(
				"root_pkg.sv",
				p.getFile("sve.f"));
		
		IFolder sub1 = SVFileUtils.mkdir(p, "sub1");
		
		SVFileUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				sub1.getFile("cls1.svh"));
		
		SVFileUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				sub1.getFile("cls2.svh"));
		
		SVFileUtils.copy(
				"class cls3;\n" +
				"endclass\n",
				p.getFile("cls3.svh"));

		runTest(p, argfile, "sub1/", 
				new String[] {"cls1.svh", "cls2.svh"});
	}
	
	void runTest(
			IProject		project,
			String			argfile,
			String			root,
			String			expected[]) {
		ISVDBFileSystemProvider fs = new SVDBWSFileSystemProvider();
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), 
				project.getName(), argfile, 
				SVDBArgFileIndexFactory.TYPE, null);
		
		index.loadIndex(new NullProgressMonitor());
		
		List<String> inc_paths = new ArrayList<String>();
		inc_paths.add(SVFileUtils.getPathParent(argfile));
		
		List<SVDBIncFileInfo> inc_files = SVDBFindIncFileUtils.findIncludeFiles(
				index, fs, inc_paths, 
				root,
				ISVDBIndex.FIND_INC_ALL_FILES);
	
		List<String> exp_l = new ArrayList<String>();
		for (int i=0; i<expected.length; i++) {
			exp_l.add(expected[i]);
		}
		
		List<String> unexp_l = new ArrayList<String>();
		for (int i=0; i<inc_files.size(); i++) {
			unexp_l.add(inc_files.get(i).getIncFile());
		}
		
		for (int i=0; i<exp_l.size(); i++) {
			int idx = unexp_l.indexOf(exp_l.get(i));
			
			if (idx != -1) {
				unexp_l.remove(idx);
				exp_l.remove(i);
				i--;
			}
		}
		
		StringBuilder missing_exp = new StringBuilder();
		StringBuilder unexpected = new StringBuilder();
	
		for (int i=0; i<exp_l.size(); i++) {
			missing_exp.append(exp_l.get(i) + " ");
		}
	
		for (int i=0; i<unexp_l.size(); i++) {
			unexpected.append(unexp_l.get(i) + " ");
		}

		assertEquals("Missing the following proposals: " + missing_exp.toString(), 
				0, missing_exp.length());
		assertEquals("Unexpected proposals: " + unexpected.toString(),
				0, unexpected.length());
	}

}

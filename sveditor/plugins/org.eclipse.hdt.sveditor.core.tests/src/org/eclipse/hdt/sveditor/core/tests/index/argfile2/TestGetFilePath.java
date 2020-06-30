/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBFilePath;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexUtil;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;

public class TestGetFilePath extends SVCoreTestCaseBase {
	
	public void testFindSVFilePath() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project = new File(fTmpDir, "project");
		File project2= new File(fTmpDir, "project2");
		File inc1    = new File(project, "inc");
		File inc2    = new File(project, "inc2");
		
		assertTrue(project.mkdirs());
		assertTrue(project2.mkdirs());
		assertTrue(inc1.mkdirs());
		assertTrue(inc2.mkdirs());
	
		File argfile_f = new File(project, "argfile.f");
		TestUtils.copy(
				"+incdir+.\n" +
				"+incdir+inc2\n" +
				"+incdir+inc\n" +
				"root_pkg.sv",
				argfile_f);
		
		File root_pkg_sv = new File(project, "root_pkg.sv");
		TestUtils.copy(
				"package root_pkg;\n" +
				"	`include \"cls1.svh\"\n" +		// In the root 
				"	`include \"cls2.svh\"\n" +		// In inc1 (copy in inc2)
				"	`include \"./cls3.svh\"\n" +	// In inc1
				"	`include \"" + fTmpDir.toString().replace('\\', '/') + 
						"/project/inc/cls4.svh\"\n" +	// Full path to file in inc 
				"	`include \"../project/cls5.svh\"\n" +	// relative path outside of the project
				"	`include \"" + fTmpDir.toString().replace('\\', '/') + "/project2/cls6.svh\"\n" +	// Full path outside of the project 
				"endpackage\n",
				root_pkg_sv);
		
		File cls1_svh = new File(project, "cls1.svh");
		TestUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				cls1_svh);
		
		// cls2.svh has been placed in both inc1 and inc2 directories.  The inc1 should NOT be picked up because
		// the incdir order is inc2 then inc1
		File cls2_svh = new File(inc1, "cls2.svh");
		TestUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				cls2_svh);

		// cls2 file ... will be picked up
		File cls2_2_svh = new File(inc2, "cls2.svh");
		TestUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				cls2_2_svh);
		
		File cls3_svh = new File(inc1, "cls3.svh");
		TestUtils.copy(
				"class cls3;\n" +
				"endclass\n",
				cls3_svh);
		
		File cls4_svh = new File(inc1, "cls4.svh");
		TestUtils.copy(
				"class cls4;\n" +
				"endclass\n",
				cls4_svh);
		
		File cls5_svh = new File(project, "cls5.svh");
		TestUtils.copy(
				"class cls5;\n" +
						"endclass\n",
						cls5_svh);
		
		File cls6_svh = new File(project2, "cls6.svh");
		TestUtils.copy(
				"class cls6;\n" +
						"endclass\n",
						cls6_svh);
		
		IProject p = TestUtils.createProject("project", project);
		addProject(p);
		
		String argfile_f_path = "${workspace_loc}/project/argfile.f";
		String inc_paths [] =  {
				// TODO - some of these are probably not right
			"${workspace_loc}/project/cls1.svh",
			"${workspace_loc}/project/inc2/cls2.svh",
			"${workspace_loc}/project/inc/./cls3.svh",
			"${workspace_loc}/project/inc/cls4.svh",
			"${workspace_loc}/project/cls5.sv",
			"${workspace_loc}/project2/cls6.svh"
			};

		ISVDBIndexCache cache = fCacheFactory.createIndexCache(
				"GLOBAL", argfile_f_path);
		ISVDBIndex index = new SVDBArgFileIndex("GLOBAL", 
				argfile_f_path,
				new SVDBWSFileSystemProvider(),
				cache, null);
		index.init(new NullProgressMonitor(), null);
	
		index.loadIndex(new NullProgressMonitor());
		
		for (String path : index.getFileList(new NullProgressMonitor())) {
			List<SVDBMarker> markers = index.getMarkers(path);
			for (SVDBMarker m : markers) {
				fLog.debug("Marker: " + m.getMessage());
			}
			assertEquals(0, markers.size());
		}
	
		IndexTestUtils.assertFileHasElements(index, 
				new String[] {"cls1", "cls2", "cls3", "cls4", "cls5"});
	}

	public void testFindArgFilePath() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project = new File(fTmpDir, "project");
		
		assertTrue(project.mkdirs());
		
		File argfile_f = new File(project, "argfile.f");
		TestUtils.copy(
				"-f argfile_s1.f",
				argfile_f);
		
		File argfile_s1_f = new File(project, "argfile_s1.f");
		TestUtils.copy(
				"-f argfile_s2.f",
				argfile_s1_f);
		
		File argfile_s2_f = new File(project, "argfile_s2.f");
		TestUtils.copy(
				"root_pkg.sv",
				argfile_s2_f);
		
		File root_pkg_sv = new File(project, "root_pkg.sv");
		TestUtils.copy(
				"package root_pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"endpackage\n",
				root_pkg_sv);
		
		File cls1_svh = new File(project, "cls1.svh");
		TestUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				cls1_svh);
		
		IProject p = TestUtils.createProject("project", project);
		addProject(p);
		
		String argfile_f_path = "${workspace_loc}/project/argfile.f";
		String argfile_s2_f_path = "${workspace_loc}/project/argfile_s2.f";

		ISVDBIndexCache cache = fCacheFactory.createIndexCache(
				"GLOBAL", argfile_f_path);
		ISVDBIndex index = new SVDBArgFileIndex("GLOBAL", 
				argfile_f_path,
				new SVDBWSFileSystemProvider(),
				cache, null);
		index.init(new NullProgressMonitor(), null);
	
		index.loadIndex(new NullProgressMonitor());
		
		List<SVDBFilePath> paths = index.getFilePath(argfile_s2_f_path);
		
		assertNotNull(paths);
		
		assertEquals(1, paths.size());
		
		SVDBFilePath path = paths.get(0);
		assertEquals(3, path.getPath().size());
	
//		for (Tuple<SVDBFileTree, ISVDBItemBase> pi : path.getPath()) {
//			System.out.println("path: " + pi.first().getFilePath());
//		}
	}

}

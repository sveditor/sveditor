/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.fileset;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.fileset.SVFilesystemFileMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class FileSetTests extends TestCase {
	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		fTmpDir.delete();
	}

	public void testDefaultRecurse() {
		SVCorePlugin.getDefault().enableDebug(true);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File t_dir = new File(fTmpDir, "testDefaultRecurse"); 
		utils.copyBundleDirToFS("/project_dir_src_collection_module", t_dir);
		
		File base = new File(t_dir, "project_dir_src_collection_module");
		
		SVFileSet fs = new SVFileSet(base.getAbsolutePath());
		
		String dflt_include = SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes();
		String dflt_exclude = SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes();
		
		fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(dflt_include));
		fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(dflt_exclude));
		
		SVFilesystemFileMatcher matcher = new SVFilesystemFileMatcher();
		matcher.addFileSet(fs);
		List<String> matches = matcher.findIncludedPaths();
		
		Set<String> match_set = new HashSet<String>();
		match_set.add("class1.svh");
		match_set.add("top.v");
		match_set.add("defines.svh");
		match_set.add("sub.v");
		match_set.add("class3.svh");
		
		for (String m : matches) {
			System.out.println("Match: " + m);
			File f = new File(m);
			assertTrue(match_set.contains(f.getName()));
			match_set.remove(f.getName());
		}
		
		assertEquals(0, match_set.size());
	}

	public void testExcludeRecurse() {
		SVCorePlugin.getDefault().enableDebug(true);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File t_dir = new File(fTmpDir, "testDefaultRecurse"); 
		utils.copyBundleDirToFS("/project_dir_src_collection_module", t_dir);
		
		File base = new File(t_dir, "project_dir_src_collection_module");
		
		SVFileSet fs = new SVFileSet(base.getAbsolutePath());
		
		String dflt_include = SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes();
		String dflt_exclude = SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes();
		
		fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(dflt_include));
		fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(dflt_exclude));
		fs.addExclude("subdir/*");
		
		SVFilesystemFileMatcher matcher = new SVFilesystemFileMatcher();
		matcher.addFileSet(fs);
		List<String> matches = matcher.findIncludedPaths();
		
		Set<String> match_set = new HashSet<String>();
		match_set.add("class1.svh");
		match_set.add("top.v");
		match_set.add("defines.svh");
		match_set.add("sub.v");
		
		for (String m : matches) {
			System.out.println("Match: " + m);
			File f = new File(m);
			assertTrue(match_set.contains(f.getName()));
			match_set.remove(f.getName());
		}
		
		assertEquals(0, match_set.size());
	}

	public void testNonRecurseVlog() {
		SVCorePlugin.getDefault().enableDebug(true);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File t_dir = new File(fTmpDir, "testDefaultRecurse"); 
		utils.copyBundleDirToFS("/project_dir_src_collection_module", t_dir);
		
		File base = new File(t_dir, "project_dir_src_collection_module");
		
		SVFileSet fs = new SVFileSet(base.getAbsolutePath());
		
		fs.addInclude("*.v");
		
		SVFilesystemFileMatcher matcher = new SVFilesystemFileMatcher();
		matcher.addFileSet(fs);
		List<String> matches = matcher.findIncludedPaths();
		
		Set<String> match_set = new HashSet<String>();
		match_set.add("top.v");
		match_set.add("sub.v");
		
		for (String m : matches) {
			System.out.println("Match: " + m);
			File f = new File(m);
			assertTrue(match_set.contains(f.getName()));
			match_set.remove(f.getName());
		}
		
		assertEquals(0, match_set.size());
	}
	
	public void testWindowsPathPattern() {
		String root = "F:\\soft\\OVM-UVM\\ovm-2.1.1\\src";
		final String input[] = {
				root + "/foo.svh",
				root + "\\foo.sv"
		};
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		SVFileSet fs = SVCorePlugin.getDefault().getDefaultFileSet(root);
		fs.addInclude("**/*.v");
		fs.addInclude("**/*.svh");
		
		AbstractSVFileMatcher matcher = new AbstractSVFileMatcher() {
			
			@Override
			public List<String> findIncludedPaths() {
				fLog = LogFactory.getLogHandle("AbstractSVFileMatcher");
				List<String> ret = new ArrayList<String>();
				
				for (String in : input) {
					if (include_file(in)) {
						ret.add(SVFileUtils.normalize(in));
					}
				}
				
				return ret;
			}
		};
		
		matcher.addFileSet(fs);
		List<String> result = matcher.findIncludedPaths();
		
		for (String exp : input) {
			exp = SVFileUtils.normalize(exp);
			assertTrue(result.contains(exp));
		}
	}

}

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
package org.eclipse.hdt.sveditor.core.tests.preproc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBEndLocation;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByNameMatcher;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class TestPreProcLineNumbers extends SVCoreTestCaseBase {
	
	class StartEnd extends Tuple<SVDBLocation, SVDBLocation> {
		public StartEnd(int s_file, int s_line, int e_file, int e_line) {
			super(new SVDBLocation(s_file, s_line, 0), new SVDBLocation(e_file, e_line, 0));
		}
	}
	
	public void testLineNumberBasics() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"\n" +
			"\n" +
			"class c;\n" +
			"	int a;\n" +
			"endclass\n"
			;
		Map<String, String> fmap = new HashMap<String, String>();
		fmap.put("/files.f", "/" + getName() + ".sv\n");
		fmap.put("/" + getName() + ".sv", doc);
		
		Map<String, Object> lmap = new HashMap<String, Object>();
		lmap.put("c", new StartEnd(1, 3, 1, 5));
		lmap.put("c.a", new SVDBLocation(1, 4, 0));
	
		runLineNumberTest(fmap, lmap);
		runLineNumberTestWinEOL(fmap, lmap);
	}

	public void testLineNumberMacro_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"\n" +                        // 1
			"`define FIELD(n) int n\n" +  // 2
			"\n" +                        // 3
			"class c;\n" +                // 4
			"	`FIELD(a);\n" +           // 5
			"endclass\n"                  // 6
			;
		Map<String, String> fmap = new HashMap<String, String>();
		fmap.put("/files.f", "/" + getName() + ".sv\n");
		fmap.put("/" + getName() + ".sv", doc);
		
		Map<String, Object> lmap = new HashMap<String, Object>();
		lmap.put("c", new StartEnd(1, 4, 1, 6));
		lmap.put("c.a", new SVDBLocation(1, 5, 0));
	
		runLineNumberTest(fmap, lmap);
		runLineNumberTestWinEOL(fmap, lmap);
	}

	public void testLineNumberMacro_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"\n" +                        		// 1
			"`define SUBFIELD(n) int n\n" +		// 2
			"`define FIELD(n) `SUBFIELD(n)\n" + // 3
			"\n" +                        		// 4
			"class c;\n" +                		// 5
			"	`FIELD(a);\n" +           		// 6
			"endclass\n"                  		// 7
			;
		Map<String, String> fmap = new HashMap<String, String>();
		fmap.put("/files.f", "/" + getName() + ".sv\n");
		fmap.put("/" + getName() + ".sv", doc);
		
		Map<String, Object> lmap = new HashMap<String, Object>();
		lmap.put("c", new StartEnd(1, 5, 1, 7));
		lmap.put("c.a", new SVDBLocation(1, 6, 0));
	
		runLineNumberTest(fmap, lmap);
		runLineNumberTestWinEOL(fmap, lmap);
	}

	public void testLineNumberMacro_3() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"\n" +									// 1
			"`define SUBFIELD(n) \\\n" +			// 2
			"   \\\n" +								// 3
			"	int n\n" +							// 4
			"`define FIELD(n) `SUBFIELD(n)\n" +  	// 5
			"\n" +                        			// 6
			"class c;\n" +                			// 7
			"	`FIELD(a);\n" +           			// 8
			"endclass\n"                  			// 9
			;
		Map<String, String> fmap = new HashMap<String, String>();
		fmap.put("/files.f", "/" + getName() + ".sv\n");
		fmap.put("/" + getName() + ".sv", doc);
		
		Map<String, Object> lmap = new HashMap<String, Object>();
		lmap.put("c", new StartEnd(1, 7, 1, 9));
		lmap.put("c.a", new SVDBLocation(1, 8, 0));
	
		runLineNumberTest(fmap, lmap);
		runLineNumberTestWinEOL(fmap, lmap);
	}

	public void testLineNumberInclude_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		String foo_svh = 
			"\n" +									// 1
			"class foo;\n" +						// 2
			"	int a;\n" +							// 3
			"endclass\n"							// 4
			;
		String doc =
			"\n" +									// 1
			"`include \"foo.svh\"\n" +				// 2
			"\n" +                        			// 3
			"class c;\n" +                			// 4
			"	int a;\n" +							// 5
			"endclass\n"                  			// 6
			;
		Map<String, String> fmap = new HashMap<String, String>();
		fmap.put("/files.f", "/" + getName() + ".sv\n");
		fmap.put("/" + getName() + ".sv", doc);
		fmap.put("/foo.svh", foo_svh);
		
		Map<String, Object> lmap = new HashMap<String, Object>();
		lmap.put("c", new StartEnd(1, 4, 1, 6));
		lmap.put("c.a", new SVDBLocation(1, 5, 0));
		lmap.put("foo", new StartEnd(2, 2, 2, 4));
		lmap.put("foo.a", new SVDBLocation(2, 3, 0));
	
		runLineNumberTest(fmap, lmap);
		runLineNumberTestWinEOL(fmap, lmap);
	}
	
	public void testMultiInclude_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String file1_svh =
			"class file1;\n" +
			"\n" +
			"endclass\n"
			;
		
		String file2_svh =
			"/**\n" +
			" * Leading comment\n" +
			" */\n" +
			"class file2;\n" +
			"\n" +
			"endclass\n";
		
		String root = 
				"\n" +
				"\n" +
				"class pre_file1;\n" +
				"endclass\n" +
				"`include \"file1.svh\"\n" + // 5
				"class post_file1;\n" +
				"endclass\n" +
				"`include \"file2.svh\"\n" +
				"class post_file2;\n" +
				"endclass\n"
				;
		
		Map<String,String> fmap = new HashMap<String,String>();
		fmap.put("/files.f", "/" + getName() + ".sv\n");
		fmap.put("/" + getName() + ".sv", root);
		fmap.put("/file1.svh", file1_svh);
		fmap.put("/file2.svh", file2_svh);
				
		Map<String, Object> lmap = new HashMap<String, Object>();
		lmap.put("pre_file1",  new StartEnd(1,3, 1,4));
		lmap.put("file1",      new StartEnd(2,1, 2,3));
		lmap.put("post_file1", new StartEnd(1,6, 1,7));
		lmap.put("file2",      new StartEnd(3,4, 3,6));
		lmap.put("post_file2", new StartEnd(1,9, 1,10));
		
		runLineNumberTest(fmap, lmap);
		runLineNumberTestWinEOL(fmap, lmap);
	}
	
	public void testMultiLineCommentPackage() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"/****************************************************************************\n" +
			" * pkg1.sv\n" +
			" ****************************************************************************/\n" +
			"\n" +
			"/**\n" +
			" * Package: pkg1\n" +
			" * \n" +
			" * TODO: Add package documentation\n" +
			" */\n" +
			"package pkg1;\n" + // 10
			"	int a;\n" +
			"	int b;\n" +
			"\n" +
			"endpackage\n" // 14
			;
		Map<String,String> fmap = new HashMap<String,String>();
		fmap.put("/files.f", "/" + getName() + ".sv\n");
		fmap.put("/" + getName() + ".sv", content);
		
		Map<String, Object> lmap = new HashMap<String, Object>();
		lmap.put("pkg1", new StartEnd(1,10, 1,14));
		
		runLineNumberTest(fmap, lmap);
		runLineNumberTestWinEOL(fmap, lmap);
	}
	
	void runLineNumberTestWinEOL(
			Map<String, String>		fmap,
			Map<String, Object>		lineinfo) {
		Map<String, String> fmap_win = new HashMap<String,String>();
		
		for (String key : fmap.keySet()) {
			String doc = fmap.get(key);
			StringBuilder sb = new StringBuilder();
			
			for (int i=0; i<doc.length(); i++) {
				if (doc.charAt(i) == '\n' && 
						(i==0 || doc.charAt(i-1) != '\r')) {
					sb.append('\r');
				}
				sb.append(doc.charAt(i));
			}
			
			fmap_win.put(key, sb.toString());
		}
	
		runLineNumberTest(fmap_win, lineinfo);
	}
	
	void runLineNumberTest(
			Map<String, String>		fmap,
			Map<String, Object>		lineinfo) {
		SVDBMapFileSystemProvider fs_provider = new SVDBMapFileSystemProvider(fmap);

		String project = getName();
		String base = "/files.f";
		
		SVDBArgFileIndex index = new SVDBArgFileIndex(project, base, fs_provider,
				fCacheFactory.createIndexCache(project, base), null);
		index.init(new NullProgressMonitor(), null);
		
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
		
		// Okay, now need to go through all the elements
		for (String key : lineinfo.keySet()) {
			ISVDBItemBase it = find(index, key);
			assertNotNull("Failed to find item " + key, it);
			
			Object line_o = lineinfo.get(key);
			assertNotNull("Failed to find line info for " + key, line_o);
			
			if (line_o instanceof StartEnd) {
				StartEnd se = (StartEnd)line_o;
				assertTrue("Item " + key + " does not have an end location",
						it instanceof ISVDBEndLocation);
				ISVDBEndLocation end_l = (ISVDBEndLocation)it;
				
				assertEquals("Start file location is incorrect: " + key,
						se.first().getFileId(),
						SVDBLocation.unpackFileId(it.getLocation()));
				
				assertEquals("Start line location is incorrect: " + key,
						se.first().getLine(),
						SVDBLocation.unpackLineno(it.getLocation()));
				
				assertEquals("End file location is incorrect: " + key,
						se.second().getFileId(),
						SVDBLocation.unpackFileId(end_l.getEndLocation()));
				
				assertEquals("End line location is incorrect: " + key,
						se.second().getLine(),
						SVDBLocation.unpackLineno(end_l.getEndLocation()));
			} else {
				SVDBLocation l = (SVDBLocation)line_o;
				
				
				assertEquals("Start file location is incorrect: " + key,
						l.getFileId(),
						SVDBLocation.unpackFileId(it.getLocation()));
				
				assertEquals("Start line location is incorrect: " + key,
						l.getLine(),
						SVDBLocation.unpackLineno(it.getLocation()));
			}
			
		}
	}
	
	ISVDBItemBase find(ISVDBIndex index, String path) {
		List<String> path_l = new ArrayList<String>();
		int pos=0;
		
		do {
			int next_d = path.indexOf('.', pos);
			
			if (next_d < 0) {
				path_l.add(path.substring(pos));
				break;
			} else {
				path_l.add(path.substring(pos, next_d));
				pos = next_d+1;
			}
		} while (true);
	
		List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				path_l.get(0), new SVDBFindByNameMatcher());
		
		assertTrue("Failed to find " + path_l.get(0), (result.size() == 1));
		
		if (path_l.size() == 1) {
			fLog.debug("  it: " + result.get(0).getName() + " " +
					result.get(0).getFilename());
			return result.get(0).getSVDBItem();
		} else {
			return find((ISVDBChildParent)result.get(0).getSVDBItem(), path_l, 1);
		}
	}
	
	ISVDBItemBase find(
			ISVDBChildParent	scope,
			List<String>		path,
			int					path_i) {
		
		for (ISVDBChildItem it : scope.getChildren()) {
			if (it instanceof ISVDBNamedItem &&
					((ISVDBNamedItem)it).getName().equals(path.get(path_i))) {
				if (path_i+1 < path.size()) {
					assertTrue("item " + path.get(path_i) + " is not a scope item",
							it instanceof ISVDBScopeItem);
					return find((ISVDBScopeItem)it, path, path_i+1);
				} else {
					return it;
				}
			} else if (it instanceof SVDBVarDeclStmt) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
				for (ISVDBChildItem vi : v.getChildren()) {
					if (((ISVDBNamedItem)vi).getName().equals(path.get(path_i))) {
						return vi;
					}
				}
			}
		}
		
		fail("Failed to find path element " + path.get(path_i));
	
		return null;
	}

}

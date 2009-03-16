package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.ISVDBIndex;
import net.sf.sveditor.core.SVDBIncludeSearch;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;

public class SVDBFileTreeUtils {
	
	private boolean			fDebugEn = false;
	private ISVDBIndex		fIndex;
	
	
	public void setIndex(ISVDBIndex index) {
		fIndex = index;
	}
	
	/**
	 * Build a data structure that describes what files are included by
	 * the indicated file, and which files include this file (and its parents).
	 * 
	 * - Also builds pre-processed SVDB structures for the fan-in
	 * 
	 * @param file
	 * @param files
	 * @return
	 */
	public SVDBFileTree createFileContext(
			SVDBFile			file,
			Map<File, SVDBFile> files) {
		SVDBFileTree       ret    = null;
		List<SVDBFileTree> file_l = new ArrayList<SVDBFileTree>();
		Iterator<SVDBFile> it = files.values().iterator();
		List<SVDBFileTree> super_inc_l = new ArrayList<SVDBFileTree>();
		
		debug("--> createFileContext(" + file.getFilePath() + ")");
		
		while (it.hasNext()) {
			SVDBFile f = it.next();
			SVDBFileTree file_t = new SVDBFileTree((SVDBFile)f.duplicate());
			
			if (file.equals(f)) {
				ret = file_t;
			}
			
			// Populate the includedFiles array
			file_l.add(file_t);
		}
		
		// Debug
		if (ret == null) {
			System.out.println("[ERROR] failed to find file \"" + file.getFilePath() + "\"");
			System.out.println("    in list:");
			it = files.values().iterator();
			while (it.hasNext()) {
				SVDBFile f = it.next();
				System.out.println("        " + f.getFilePath());
			}
		}
		
		// First, determine whether any files include this file
		// Only pick one
		SVDBFileTree super_inc = ret;

		super_inc_l.add(ret);
		
		while (super_inc != null && (super_inc = findIncParent(super_inc, file_l)) != null) {
			super_inc_l.add(super_inc);
			
			if (super_inc_l.size() > 100) {
				System.out.println("[ERROR] super-include chain >100");
			}
		}
		
		if (fDebugEn) {
			debug("include chain for " + ret.getFilePath() + " is " + 
					super_inc_l.size() + " long");
			for (SVDBFileTree ft : super_inc_l) {
				debug("    " + ft.getFilePath());
			}
		}
		
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider();
		dp.setFileContext(ret);

		for (int i=super_inc_l.size()-1; i>=0; i--) {
			if (i > 0) {
				super_inc_l.get(i-1).getIncludedByFiles().add(
						super_inc_l.get(i));
			}
			if (ret == super_inc_l.get(i)) {
				debug("processing target file");
			}
			processFile(dp, super_inc_l.get(i), file_l);
		}
		
		if (fDebugEn) {
			debug("Included Files:");
			for (SVDBFileTree t : ret.getIncludedFiles()) {
				debug("    " + t.getFilePath());
			}
			
			debug("Included-by Files:");
			for (SVDBFileTree t : ret.getIncludedByFiles()) {
				debug("    " + t.getFilePath());
			}
		}
		
		debug("<-- createFileContext(" + file.getFilePath() + ")");
		
		return ret;
	}
	
	public void resolveConditionals(SVDBFileTree file) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider();
		dp.setFileContext(file);
		
		processScope(file.getSVDBFile(), dp, file, null);
	}
	
	private SVDBFileTree findIncParent(
			SVDBFileTree 			file, 
			List<SVDBFileTree>		file_l) {
		SVDBFileTree ret = null;
		debug("--> findIncParent(" + file.getFilePath() + ")");
		
		for (SVDBFileTree ft : file_l) {
			debug("    checking file " + ft.getFilePath());
			if (includesFile(ft.getSVDBFile(), file)) {
				debug("        INCLUDES FILE");
				if (ret != null) {
					// more than one file matches the include-file path
					// determine which files matches best
					ret = findBestIncParent(file, ret, ft);
				} else {
					ret = ft;
				}
			}
		}
		
		debug("<-- findIncParent(" + file.getFilePath() + ")");
		return ret;
	}
	
	private static SVDBFileTree findBestIncParent(
			SVDBFileTree		file,
			SVDBFileTree		p1,
			SVDBFileTree		p2) {
		File file_dir = file.getFilePath().getParentFile();
		File p1_dir   = p1.getFilePath().getParentFile();
		File p2_dir   = p2.getFilePath().getParentFile();

		if (file_dir.equals(p1_dir) && !file_dir.equals(p2_dir)) {
			return p1;
		} else if (file_dir.equals(p2_dir) && !file_dir.equals(p1_dir)) {
			return p2;
		} else {
			//
			System.out.println("[TODO] Both p1 and p2 are in the same dir");
			System.out.println("    file=" + file.getFilePath());
			System.out.println("        p1=" + p1.getFilePath());
			System.out.println("        p2=" + p2.getFilePath());
			
			return p1;
		}
	}
	
	/**
	 * Checks whether file includes file_t
	 * 
	 * @param file
	 * @param file_t
	 * @return
	 */
	private boolean includesFile(SVDBScopeItem file, SVDBFileTree file_t) {
		boolean ret = false;
		
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Include) {
				if (file_t.getFilePath().getPath().endsWith(it.getName())) {
					ret = true;
				}
			} else if (it.getType() == SVDBItemType.PreProcCond ||
					it.getType() == SVDBItemType.PackageDecl) {
				ret |= includesFile((SVDBScopeItem)it, file_t);
			}
			
			if (ret) {
				break;
			}
		}
		
		return ret;
	}
	
	private void processFile(
			SVPreProcDefineProvider	dp,
			SVDBFileTree 			file, 
			List<SVDBFileTree> 		file_l) {
		debug("--> processFile(" + file.getFilePath() + ")");
		
		// to prevent later recursion, mark this as processed now
		file.setFileProcessed(true);

		// Setup strategy is slighty different
		// - Beginning with this file, scan out to the included-by list
		//   - The idea is that, since this file would be included in 
		//     its parent, it should be processed in the context of that
		//     parent
		// - Process included files
		//   - handle conditionals
		//   - process included files
		
		// Resolve conditionals and follow includes in this file
		processScope(file.getSVDBFile(), dp, file, file_l);

		if (fDebugEn) {
			debug("   File \"" + file.getFilePath() + "\" complete");
			for (SVDBFileTree f : file.getIncludedFiles()) {
				debug("        Included - " + f.getFilePath());
			}
			for (SVDBFileTree f : file.getIncludedByFiles()) {
				debug("        Included-By - " + f.getFilePath());
			}
		}
		
		debug("<-- processFile(" + file.getFilePath() + ")");
	}
	
	/**
	 * Process 'scope' for pre-processor conditionals
	 * 
	 * @param scope
	 * @param dp
	 * @param file
	 * @param file_l
	 */
	private void processScope(
			SVDBScopeItem			scope,
			SVPreProcDefineProvider	dp,
			SVDBFileTree 			file, 
			List<SVDBFileTree> 		file_l) {
		List<SVDBItem> it_l = scope.getItems(); 
		
		for (int i=0; i<it_l.size(); i++) {
			SVDBItem it = it_l.get(i);
			
			if (it.getType() == SVDBItemType.PreProcCond) {
				SVDBPreProcCond c = (SVDBPreProcCond)it;
				
				debug("    pre-proc conditional " + c.getName() + " " + c.getConditional());
				
				String cond = c.getConditional();
				boolean defined = dp.isDefined(cond, it.getLocation().getLine());
				if ((defined && c.getName().equals("ifdef")) ||
						(!defined && c.getName().equals("ifndef"))) {
					// Remove any 'else' section
					if (i+1 < it_l.size()) {
						SVDBItem it_t = it_l.get(i+1);
						if (it_t.getType() == SVDBItemType.PreProcCond &&
								it_t.getName().equals("else")) {
							debug("        removing else section");
							it_l.remove(i+1);
						}
					}
					
					// pull this section up
					it_l.remove(i);
					if (fDebugEn) {
						debug("        adding enabled items (" + c.getName() + ")");
						for (SVDBItem it_t : c.getItems()) {
							debug("            " + it_t.getType() + " " + it_t.getName());
						}
					}
					it_l.addAll(i, c.getItems());
					
					i--;
				} else {
					// remove this section
					it_l.remove(i);
					
					// If the following section is 'else', pull up contents
					if (i < it_l.size()) {
						SVDBItem it_t = it_l.get(i);
						debug("    following disabled section: " + it_t.getName());
						if (it_t.getType() == SVDBItemType.PreProcCond &&
								it_t.getName().equals("else")) {
							it_l.remove(i);
							if (fDebugEn) {
								debug("    adding enabled items from 'else'");
								for (SVDBItem it_tt : ((SVDBPreProcCond)it_t).getItems()) {
									debug("            " + it_tt.getType() + " " + it_tt.getName());
								}
							}
							it_l.addAll(i, ((SVDBPreProcCond)it_t).getItems());
						}
					}
					i--;
				}
			} else if (it.getType() == SVDBItemType.Include) {
				if (file_l != null) {
					// TODO: opportunity for caching here

					// Find the include in the file list and process
					SVDBFileTree inc_file = findIncludedFile(file, it.getName(), file_l);
					
					if (inc_file == null && fIndex != null) {
						SVDBFile f = new SVDBIncludeSearch(fIndex).findIncludedFile(it.getName());
						
						if (f != null) {
							inc_file = new SVDBFileTree((SVDBFile)f.duplicate());
						}
					}

					if (inc_file == null) {
						System.out.println("[ERROR] cannot resolve inclusion \"" + 
								it.getName() + "\"");
						System.out.println("    superIndex=" + fIndex);
						
						try {
							throw new Exception();
						} catch (Exception e) {
							e.printStackTrace();
						}
					} else if (!file.getIncludedFiles().contains(inc_file)) {
						debug("    include file \"" + it.getName() + "\"");
						file.getIncludedFiles().add(inc_file);

						if (!inc_file.getFileProcessed()) {
							processFile(dp, inc_file, file_l);
						}
					} else {
						debug("    file \"" + inc_file.getFilePath() + "\" already included");
					}
				}
			} else if (it.getType() == SVDBItemType.PackageDecl) {
				processScope((SVDBScopeItem)it, dp, file, file_l);
			}
		}
	}
	
	
	/**
	 * Given a list of SVDBFiles from the SVPreProcScanner, resolve the
	 * `include relationships between these files
	 * 
	 * @param files
	 */
	public static Map<File, SVDBFileTree> organizeFiles(List<SVDBFile> files) {
		Map<File, SVDBFileTree> file_map = new HashMap<File, SVDBFileTree>();
		List<SVDBFileTree> org_files = new ArrayList<SVDBFileTree>();
		
		for (SVDBFile f : files) {
			SVDBFileTree file_t = new SVDBFileTree(f);
			// Populate the includedFiles array
			setupIncludedFiles(file_t, f);
			org_files.add(file_t);
		}
		
		// Now, crawl through the list and resolve the inclusions
		for (SVDBFileTree file_t : org_files) {
			resolveInclusions(file_t, org_files);
		}
		
		// Next, revisit the list to setup lists of included references
		for (SVDBFileTree file_t : org_files) {
			resolveIncludedRefs(file_t, org_files);
		}
		
		for (SVDBFileTree file_t : org_files) {
			file_map.put(file_t.getFilePath(), file_t);
		}

		return file_map;
	}
	
	private static void setupIncludedFiles(
			SVDBFileTree			file_t,
			SVDBFile				file) {
		for (SVDBItem it : file.getItems()) {
			if (it instanceof SVDBInclude) {
				SVDBFileTree t = new SVDBFileTree(new File(it.getName()));
				file_t.getIncludedFiles().add(t);
			} else if (it instanceof SVDBPackageDecl) {
				for (SVDBItem it_p : ((SVDBPackageDecl) it).getItems()) {
					if (it_p instanceof SVDBInclude) {
						SVDBFileTree t = new SVDBFileTree(new File(it_p.getName()));
						file_t.getIncludedFiles().add(t);
					}
				}
			}
		}
	}
	
	private SVDBFileTree findIncludedFile(
			SVDBFileTree		file_t,
			String				name,
			List<SVDBFileTree>	file_l) {
		SVDBFileTree inc_file = null;

		for (SVDBFileTree f : file_l) {
			if (f.getFilePath().getPath().endsWith(name)) {
				if (inc_file != null) {
					System.out.println("[WARN] multiple files match " +
							"include \"" + name + "\""); 
					inc_file = findBestIncParent(file_t, inc_file, f);
				} else {
					inc_file = f;
				}
			}
		}
		
		return inc_file;
	}
	
	private static void resolveInclusions(
			SVDBFileTree 		file_t, 
			List<SVDBFileTree> 	files) {
		for (int i=0; i<file_t.getIncludedFiles().size(); i++) {
			SVDBFileTree f = file_t.getIncludedFiles().get(i);
			SVDBFileTree inc_file = null;

			if (f.getSVDBFile() == null) {
				// Search the top-level list
				for (SVDBFileTree ft : files) {
					// TODO: must account for other files with the same name
					// - Use distance as a similarity metric?
					if (ft.getFilePath().getPath().endsWith(f.getFilePath().getPath())) {
						if (inc_file != null) {
							// inc_file = determineClosestMatch(file_t, f, inc_file, ft);
						} else {
							inc_file = ft;
						}
					}
				}
				
				if (inc_file != null) {
					file_t.getIncludedFiles().set(i, inc_file);
				} else {
					System.out.println("Could not resolve inc \"" + 
							f.getFilePath() + "\"");
				}
			}
		}
	}
	
	/*
	private static SVDBFileTree determineClosestMatch(
			SVDBFileTree		inc_file,
			SVDBFileTree		f1,
			SVDBFileTree		f2) {
		System.out.println("determineClosestMatch: include \"" + 
				inc_path.getFilePath() + "\" in file \"" + 
				inc_file.getFilePath() + "\"");
		System.out.println("    f1: " + f1.getFilePath());
		System.out.println("    f2: " + f2.getFilePath());
		
		return f1;
	}
	  */

	private static void resolveIncludedRefs(
			SVDBFileTree 		file_t, 
			List<SVDBFileTree> 	files) {
		for (SVDBFileTree f : files) {
			for (SVDBFileTree fi : f.getIncludedFiles()) {
				//if (fi.equals(file_t)) {
				if (fi.getFilePath().equals(file_t.getFilePath())) {
					if (!file_t.getIncludedByFiles().contains(f)) {
						file_t.getIncludedByFiles().add(f);
					}
				}
			}
		}
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}

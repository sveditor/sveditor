/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPreProcCond;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.scanner.IDefineProvider;

public class SVDBFileTreeUtils {
	
	private boolean						fDebugEn = false;
	private ISVDBIndex					fIndex;

	public SVDBFileTreeUtils() {
	}
	
	public void setIndex(ISVDBIndex index) {
		fIndex = index;
	}
	
	public void resolveConditionals(SVDBFileTree file, IDefineProvider dp) {
		
		processScope(file.getSVDBFile(), dp, file, null);
	}
	
	private static SVDBFileTree findBestIncParent(
			SVDBFileTree		file,
			SVDBFileTree		p1,
			SVDBFileTree		p2) {
		File file_dir = new File(file.getFilePath()).getParentFile();
		File p1_dir   = new File(p1.getFilePath()).getParentFile();
		File p2_dir   = new File(p2.getFilePath()).getParentFile();

		if (file_dir.equals(p1_dir) && !file_dir.equals(p2_dir)) {
			return p1;
		} else if (file_dir.equals(p2_dir) && !file_dir.equals(p1_dir)) {
			return p2;
		} else {
			/*
			System.out.println("[TODO] Both p1 and p2 are in the same dir");
			System.out.println("    file=" + file.getFilePath());
			System.out.println("        p1=" + p1.getFilePath());
			System.out.println("        p2=" + p2.getFilePath());
			 */
			
			return p1;
		}
	}
	
	private void processFile(
			IDefineProvider			dp,
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
			for (String f : file.getIncludedFiles()) {
				debug("        Included - " + f);
			}
			for (String f : file.getIncludedByFiles()) {
				debug("        Included-By - " + f);
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
			IDefineProvider			dp,
			SVDBFileTree 			file, 
			List<SVDBFileTree> 		file_l) {
		List<ISVDBItemBase> it_l = scope.getItems();
		debug("processScope: " + scope.getName());
		
		for (int i=0; i<it_l.size(); i++) {
			ISVDBItemBase it = it_l.get(i);
			
			if (it.getType() == SVDBItemType.PreProcCond) {
				SVDBPreProcCond c = (SVDBPreProcCond)it;
				
				debug("cond=" + c.getConditional());
				
				debug("    pre-proc conditional " + c.getName() + " " + c.getConditional());
				
				String cond = c.getConditional();
				boolean defined = dp.isDefined(cond, it.getLocation().getLine());
				if ((defined && c.getName().equals("ifdef")) ||
						(!defined && c.getName().equals("ifndef"))) {

					// Remove any 'else' or 'elsif' sections
					while (i+1 < it_l.size() && 
							it_l.get(i+1).getType() == SVDBItemType.PreProcCond &&
							(((ISVDBNamedItem)it_l.get(i+1)).getName().equals("else") ||
							 ((ISVDBNamedItem)it_l.get(i+1)).getName().equals("elsif"))) {
						debug("        removing else section");
						it_l.remove(i+1);
					}
					
					// pull this section up
					// Remove the 'ifdef' block and merge in the sub items
					it_l.remove(i);
					if (fDebugEn) {
						debug("        adding enabled items (" + c.getName() + ")");
						for (ISVDBItemBase it_t : c.getChildren()) {
							debug("            " + it_t.getType() + " " + 
									(((it_t instanceof ISVDBNamedItem))?
											((ISVDBNamedItem)it_t).getName():"UNNAMED"));
						}
					}
					it_l.addAll(i, c.getItems());
					
					i--;
				} else {
					boolean taken = false;
					
					// remove the 'ifdef'/'ifndef' block
					it_l.remove(i);
					
					// Step through any elsif statements searching for a 'taken' block
					while (i < it_l.size() && 
							it_l.get(i).getType() == SVDBItemType.PreProcCond &&
							 ((ISVDBNamedItem)it_l.get(i)).getName().equals("elsif")) {
						String elsif_cond = ((SVDBPreProcCond)it_l.get(i)).getConditional();
						taken = dp.isDefined(elsif_cond, it.getLocation().getLine());
						
						if (taken) {
							break;
						}
						
						// Remove the un-taken elsif
						it_l.remove(i);
					}
					
					if (taken) {
						// We found an elsif section where the conditional
						// evaluated to 'true'
						//
						// Move up this section
						// Eliminate all following else/elsif sections
						ISVDBItemBase it_t = it_l.get(i);
						it_l.remove(i);
						it_l.addAll(i, ((SVDBPreProcCond)it_t).getItems());
						
						while (i < it_l.size() &&
							it_l.get(i+1).getType() == SVDBItemType.PreProcCond &&
							 (((ISVDBNamedItem)it_l.get(i)).getName().equals("elsif") ||
								((ISVDBNamedItem)it_l.get(i)).getName().equals("else"))) {
							it_l.remove(i);
						}
					} else {
						// We didn't find an elsif section where the conditional
						// evaluated to 'true'
						//
						// If an 'else' block exists, then move the content up
						if (i < it_l.size()) {
							ISVDBItemBase it_t = it_l.get(i);
							debug("    following disabled section: " + SVDBItem.getName(it_t)); 
							if (it_t.getType() == SVDBItemType.PreProcCond &&
									((ISVDBNamedItem)it_t).getName().equals("else")) {
								it_l.remove(i);
								if (fDebugEn) {
									debug("    adding enabled items from 'else'");
									for (ISVDBItemBase it_tt : ((SVDBPreProcCond)it_t).getItems()) {
										debug("            " + it_tt.getType() + " " + 
												((it_tt instanceof ISVDBNamedItem)?((ISVDBNamedItem)it_tt).getName():"UNNAMED"));
									}
								}
								it_l.addAll(i, ((SVDBPreProcCond)it_t).getItems());
							}
						}
					}
					
					// If the following section is 'else', pull up contents
					i--;
				}
			} else if (it.getType() == SVDBItemType.Include) {
				SVDBInclude inc = (SVDBInclude)it;
				debug("Include File: " + inc.getName());
				
				if (file_l == null) {
					debug("[ERROR] file_l == null");
				}
				
				if (file_l != null) {
					// TODO: opportunity for caching here

					// Find the include in the file list and process
					SVDBFileTree inc_file = findIncludedFile(file, inc.getName(), file_l);
					
					if (inc_file == null && fIndex != null) {
						SVDBFile f = new SVDBIncludeSearch(fIndex).findIncludedFile(inc.getName());
						
						if (f != null) {
							inc_file = new SVDBFileTree((SVDBFile)f.duplicate());
						}
					}

					if (inc_file == null) {
						System.out.println("[ERROR] cannot resolve inclusion \"" + 
								inc.getName() + "\"");
						
						try {
							throw new Exception();
						} catch (Exception e) {
							e.printStackTrace();
						}
					} else if (!file.getIncludedFiles().contains(inc_file.getFilePath())) {
						debug("    include file \"" + inc.getName() + "\"");
						file.addIncludedFile(inc_file.getFilePath());

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
	
	private SVDBFileTree findIncludedFile(
			SVDBFileTree		file_t,
			String				name,
			List<SVDBFileTree>	file_l) {
		SVDBFileTree inc_file = null;
		boolean multi_inc = false;

		for (SVDBFileTree f : file_l) {
			if (f.getFilePath().endsWith(name)) {
				if (inc_file != null) {
					System.out.println("[WARN] multiple files match " +
							"include \"" + name + "\""); 
					inc_file = findBestIncParent(file_t, inc_file, f);
					multi_inc = true;
				} else {
					inc_file = f;
				}
			}
		}
		
		if (multi_inc) {
			System.out.println("Resolved multi-inclusion of \"" + name + 
					"\" in \"" + file_t.getFilePath() + "\" with \"" + 
					inc_file.getFilePath() + "\"");
		}
		
		return inc_file;
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}

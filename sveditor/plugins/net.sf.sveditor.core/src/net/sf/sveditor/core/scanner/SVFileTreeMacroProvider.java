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


package net.sf.sveditor.core.scanner;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVFileTreeMacroProvider implements IPreProcMacroProvider, ILogLevel {
	private ISVDBIndexCache					fIndexCache;
	private Map<String, SVDBMacroDef>		fMacroCache;
	private Set<String>						fMissingIncludes;
	private SVDBFileTree					fContext;
	private boolean							fFirstSearch;
	private int								fLastLineno;
	private LogHandle						fLog;
	private static final boolean			fDebugEn = false;
	
	public SVFileTreeMacroProvider(ISVDBIndexCache cache, SVDBFileTree context, Set<String> missing_includes) {
		fLog = LogFactory.getLogHandle("SVFileTreeMacroProvider");
		
		fContext = context;
		fIndexCache = cache;
		fMacroCache = new HashMap<String, SVDBMacroDef>();
		if (missing_includes != null) {
			fMissingIncludes = missing_includes;
		} else {
			fMissingIncludes = new HashSet<String>();
		}
		fFirstSearch = true;
		fLastLineno  = 0;
	}

	public void addMacro(SVDBMacroDef macro) {
		if (fMacroCache.containsKey(macro.getName())) {
			fMacroCache.remove(macro.getName());
		}
		fMacroCache.put(macro.getName(), macro);
	}

	public void setMacro(String key, String value) {
		if (fMacroCache.containsKey(key)) {
			fMacroCache.get(key).setDef(value);
		} else {
			fMacroCache.put(key, 
					new SVDBMacroDef(key, value));
		}
	}

	public SVDBMacroDef findMacro(String name, int lineno) {
		if (fFirstSearch) {
			collectParentFileMacros();
			fFirstSearch = false;
		}
		if (fLastLineno < lineno) {
			Set<String> processed_paths = new HashSet<String>();
			collectThisFileMacros(processed_paths, lineno);
			fLastLineno = lineno;
		}
		
		SVDBMacroDef m = fMacroCache.get(name);
		
		/*
		fLog.debug("findMacro(\"" + name + "\") => " + ((m != null)?"Defined":"Undefined") +
				" (" + fContext.getFilePath() + ")");
		 */
		
		return m; 
	}
	
	private void collectParentFileMacros() {
		List<SVDBFileTree> file_list = new ArrayList<SVDBFileTree>();
		if (fDebugEn) {
			fLog.debug("collectParentFileMacros()");
		}
		
		if (fContext == null) {
			// Nothing useful to do here
			return;
		}
		
		SVDBFileTree ib = fContext;
		file_list.add(ib);
		while (ib.getIncludedByFiles().size() > 0) {
			String ib_s = ib.getIncludedByFiles().get(0); 
			ib = fIndexCache.getFileTree(new NullProgressMonitor(), ib_s, false);
			file_list.add(ib);
		}
		
		for (int i=file_list.size()-1; i>0; i--) {
			SVDBFile this_file = file_list.get(i).getSVDBFile();
			SVDBFile next_file = file_list.get(i-1).getSVDBFile();
			if (fDebugEn) {
				fLog.enter("--> Processing file \"" + this_file.getName() + 
						"\" (next " + next_file.getName() + ")");
			}
			
			if (this_file != null) {
				collectMacroDefs(file_list.get(i), this_file, next_file);
			}
			
			if (fDebugEn) {
				fLog.leave("<-- Processing file \"" + this_file.getName() + 
						"\" (next " + next_file.getName() + ")");
			}
		}
	}
	
	private boolean collectMacroDefs(
			SVDBFileTree		file,
			ISVDBScopeItem 		scope, 
			SVDBFile 			stop_pt) {
		for (ISVDBItemBase it : scope.getItems()) {
			if (it.getType() == SVDBItemType.MacroDef) {
				/*
				fLog.debug("Adding macro \"" + it.getName() + "\"" +
						" (" + fContext.getFilePath() + ")");
				 */
				addMacro((SVDBMacroDef)it);
			} else if (it.getType() == SVDBItemType.Include) {
				String leaf = ((ISVDBNamedItem)it).getName();
				if (stop_pt != null && stop_pt.getName().endsWith(
						((ISVDBNamedItem)it).getName())) {
					/*
					fLog.debug("Found stop point");
					 */
					return true;
				} else if (!fMissingIncludes.contains(leaf)) {
					// Look for the included file
					SVDBFileTree inc = null;
					if (fDebugEn) {
						fLog.debug("Searching included files of " + file.getFilePath() + " for " + leaf);
					}
					for (String inc_s : file.getIncludedFiles()) {
						SVDBFileTree inc_t = fIndexCache.getFileTree(new NullProgressMonitor(), inc_s, false);
						
						if (inc_t != null) {
							if (fDebugEn) {
								fLog.debug("    Checking " + inc_t.getFilePath());
							}
							if (inc_t.getFilePath().endsWith(leaf)) {
								inc = inc_t;
								break;
							}
						} else {
							fLog.debug("Failed to find include FileTree \"" + inc_s + "\"");
						}
					}
					
					if (inc != null) {
						if (inc.getSVDBFile() != null) {
							collectMacroDefs(inc, inc.getSVDBFile(), null);
						}
					} else {
						fMissingIncludes.add(leaf);
						fLog.debug("Failed to find \"" + leaf + "\" in file-tree");
						if (fDebugEn) {
							for (String inc_s : file.getIncludedFiles()) {
								fLog.debug("    " + inc_s);
							}
						}
					}
				}
			} else if (it instanceof ISVDBScopeItem) {
				if (collectMacroDefs(file, (ISVDBScopeItem)it, stop_pt)) {
					return true;
				}
			}
		}
		
		return false;
	}
	
	private void collectThisFileMacros(Set<String> processed_paths, int lineno) {
		collectThisFileMacros(processed_paths, fContext, fContext.getSVDBFile(), lineno);
	}
	
	private boolean collectThisFileMacros(
			Set<String>				processed_paths,
			SVDBFileTree			context,
			ISVDBScopeItem 			scope, 
			int 					lineno) {
		for (ISVDBItemBase it : scope.getItems()) {
			if (it.getLocation() != null && 
					it.getLocation().getLine() > lineno && lineno != -1) {
				return false;
			} else if (it instanceof ISVDBScopeItem) {
				if (!collectThisFileMacros(processed_paths, context, (ISVDBScopeItem)it, lineno)) {
					return false;
				}
			} else if (it.getType() == SVDBItemType.MacroDef) {
				if (fDebugEn) {
					fLog.debug("Add macro \"" + ((ISVDBNamedItem)it).getName() + "\" from scope " + 
							((ISVDBNamedItem)scope).getName() + 
							" to " + fContext.getFilePath());
				}
				addMacro((SVDBMacroDef)it);
			} else if (it.getType() == SVDBItemType.Include) {
				// Look for the included file
				if (fDebugEn) {
					fLog.debug("Looking for include \"" + ((ISVDBNamedItem)it).getName() + "\" in FileTree " + context.getFilePath());
				}
				SVDBFileTree inc = null;
				String it_leaf = new File(((ISVDBNamedItem)it).getName()).getName();
				if (!fMissingIncludes.contains(it_leaf)) {
					if (fDebugEn) {
						List<String> inc_f = context.getIncludedFiles();
						fLog.debug("    There are " + ((inc_f != null)?inc_f.size():"null") + " included files");
					}
					for (String inc_s : context.getIncludedFiles()) {
						SVDBFileTree inc_t = fIndexCache.getFileTree(new NullProgressMonitor(), inc_s, false);
						if (fDebugEn) {
							fLog.debug("    inc_s: " + inc_s + " -> " + inc_t);
						}

						if (inc_t != null) {
							if (fDebugEn) {
								fLog.debug("    Checking file \"" + inc_t.getFilePath() + "\"");
							}
							String inc_t_leaf = new File(inc_t.getFilePath()).getName();
							if (inc_t_leaf.equals(it_leaf)) { // inc_t.getFilePath().endsWith("/" + it.getName())) {
								// if (inc_t.getFilePath().endsWith(it.getName())) {
								inc = inc_t;
								break;
							}
						}
					}
				
					if (inc != null) {
						if (inc.getSVDBFile() != null) {
							// Collect all macros
							String path = inc.getSVDBFile().getFilePath();
							if (!processed_paths.contains(path)) {
								processed_paths.add(path);
								collectThisFileMacros(processed_paths, inc, inc.getSVDBFile(), -1);
							}
						} else {
							if (fDebugEn) {
								fLog.debug("Include file \"" + inc.getFilePath() + "\" missing");
							}
						}
					} else {
						fLog.debug(LEVEL_MIN, "Failed to find \"" + SVDBItem.getName(it) + "\" in this-file-tree");
						fMissingIncludes.add(it_leaf);
						if (fDebugEn) {
							for (String inc_s : context.getIncludedFiles()) {
								fLog.debug("    " + inc_s);
							}
						}
					}
				}
			}
		}
		
		return true;
	}

}

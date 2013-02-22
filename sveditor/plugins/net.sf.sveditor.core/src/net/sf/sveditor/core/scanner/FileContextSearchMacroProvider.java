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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;

public class FileContextSearchMacroProvider implements IPreProcMacroProvider {
	private Map<String, SVDBMacroDef>	fMacroCache;
	private ISVDBIndexCache				fIndexCache;
	private Map<String, SVDBFileTree>	fWorkingSet;
	private SVDBFileTree				fContext;
	private boolean						fSearchedDown;
	private boolean						fSearchedUp;
	private boolean						fDebugEnS = false;
	private int							fIndent = 0;
	private LogHandle					fLog;
	
	
	public FileContextSearchMacroProvider(
			ISVDBIndexCache 				cache,
			Map<String, SVDBFileTree>		working_set) {
		fIndexCache = cache;
		fWorkingSet = working_set;
		fMacroCache = new HashMap<String, SVDBMacroDef>();
		fLog = LogFactory.getLogHandle("FileContextSearchMacroProvider");
	}
	
	public void setFileContext(SVDBFileTree context) {
		fContext = context;
	}

	public void addMacro(SVDBMacroDef macro) {
		if (fMacroCache.containsKey(macro.getName())) {
			fMacroCache.remove(macro.getName());
		}
		fMacroCache.put(macro.getName(), macro);
	}

	public SVDBMacroDef findMacro(String name, int lineno) {
		if (fMacroCache.containsKey(name)) {
			return fMacroCache.get(name);
		} else {
			return searchContext(fContext, name);
		}
	}

	public void setMacro(String key, String value) {
		if (fMacroCache.containsKey(key)) {
			fMacroCache.get(key).setDef(value);
		} else {
			SVDBMacroDef def = new SVDBMacroDef(key, value);
			fMacroCache.put(key, def);
		}
	}

	/**
	 * Search the given context for the named macro
	 * 
	 * Strategy is:
	 * - Search the current context for the named macro
	 * - Search the files included in the current context
	 * - Search up the include tree  
	 * @param context
	 * @param key
	 * @return
	 */
	protected SVDBMacroDef searchContext(
			SVDBFileTree 	context,
			String 			key) {
		SVDBMacroDef ret;
		if (fDebugEnS) {
			debug_s(indent(fIndent++) + "--> searchContext(" + context.getFilePath() + ", \"" + key + "\")");
		}
		
		if (!fSearchedDown) {
			searchDown(context, context, key);
			fSearchedDown = true;
		}
		
		if (fMacroCache.containsKey(key)) {
			ret = fMacroCache.get(key);
		} else if (!fSearchedUp) {
			for (String ib_s : context.getIncludedByFiles()) {
				SVDBFileTree ib; 
				if (fWorkingSet.containsKey(ib_s)) {
					ib = fWorkingSet.get(ib_s);
				} else {
					ib = fIndexCache.getFileTree(new NullProgressMonitor(), ib_s, false);
				}
				if (ib == null) {
					fLog.error("Failed to obtain path \"" + ib_s + "\" from the FileTree Cache");
					fLog.error("    File context is: " + fContext.getFilePath());
					continue;
				}
				ret = searchUp(context, ib, context, key);
			}
			fSearchedUp = true;
		}
		
		ret = fMacroCache.get(key);
		
		if (fDebugEnS) {
			debug_s(indent(--fIndent) + "<-- searchContext(" + context.getFilePath() + ", \"" + key + "\"");
		}
		return ret;
	}
	
	/**
	 * Search the specified scope and any sub-scopes
	 * 
	 * @param file
	 * @param context
	 * @param key
	 * @return
	 */
	private SVDBMacroDef searchLocal(SVDBFileTree file, ISVDBScopeItem context, String key) {
		SVDBMacroDef m = null;
		if (fDebugEnS) {
			debug_s(indent(fIndent++) + "--> searchLocal(" + file.getFilePath() + ", \"" + key + "\"");
		}

		for (ISVDBItemBase it : context.getItems()) {
			if (fDebugEnS) {
				debug_s("    it=" + ((ISVDBNamedItem)it).getName());
			}
			if (it.getType() == SVDBItemType.MacroDef) {
				SVDBMacroDef mt = (SVDBMacroDef)it;
				fMacroCache.put(mt.getName(), mt);
			} else if (it instanceof ISVDBScopeItem) {
				m = searchLocal(file, (ISVDBScopeItem)it, key);
			}
		}

		if (fDebugEnS) {
			debug_s(indent(--fIndent) + "<-- searchLocal(" + file.getFilePath() + ", \"" + key + "\"");
		}
		return m;
	}
	
	private SVDBMacroDef searchDown(SVDBFileTree boundary, SVDBFileTree context, String key) {
		SVDBMacroDef m = null;

		if (fDebugEnS) {
			debug_s(indent(fIndent++) + "--> searchDown(" + context.getFilePath() + ", \"" + key + "\")");
		}

		if (context.getSVDBFile() != null) {
			searchLocal(context, context.getSVDBFile(), key);
			for (String inc_s : context.getIncludedFiles()) {
				SVDBFileTree inc;
				if (fWorkingSet.containsKey(inc_s)) {
					inc = fWorkingSet.get(inc_s);
				} else {
					inc = fIndexCache.getFileTree(new NullProgressMonitor(), inc_s, false);
				}

				if (fDebugEnS) {
					debug_s(indent(fIndent) + "    searching included file \"" + ((inc !=null)?inc.getFilePath():"NULL") + "\"");
				}
				if (inc != null && inc.getSVDBFile() != null) {
					searchDown(boundary, inc, key);
				}
			}
		}
	
		if (fDebugEnS) {
			debug_s(indent(--fIndent) + "<-- searchDown(" + context.getFilePath() + ", \"" + key + "\")");
		}
		return m;
	}
	
	/**
	 * Search up the file tree. 
	 * 
	 * @param context - The context to search
	 * @param child   - The file that is included by context
	 * @param key     - 
	 * @return
	 */
	private SVDBMacroDef searchUp(
			SVDBFileTree	boundary,
			SVDBFileTree 	context,
			SVDBFileTree	child,
			String 			key) {
		SVDBMacroDef m = null;

		if (fDebugEnS) {
			debug_s(indent(fIndent++) + "--> searchUp(" + context.getFilePath() + ", " + key + ")");
		}
		
		searchLocal(context, context.getSVDBFile(), key);
		List<String> inc_files = context.getIncludedFiles();
		synchronized (inc_files) {
			for (String is_s : inc_files) {
				SVDBFileTree is;
				if (fWorkingSet.containsKey(is_s)) {
					is = fWorkingSet.get(is_s);
				} else {
					is = fIndexCache.getFileTree(new NullProgressMonitor(), is_s, false);
				}

				if (is == null) {
					// File doesn't exist
					continue;
				}

				if (!is.getFilePath().equals(child.getFilePath()) && (is != boundary)) {
					if (fDebugEnS) {
						debug_s(indent(fIndent) + "    included file: " + is.getFilePath());
					}

					searchDown(boundary, is, key);
					for (String ib_s : context.getIncludedByFiles()) {
						SVDBFileTree ib;
						if (fWorkingSet.containsKey(ib_s)) {
							ib = fWorkingSet.get(ib_s);
						} else {
							ib = fIndexCache.getFileTree(new NullProgressMonitor(), ib_s, false);
						}
						searchUp(boundary, ib, context, key);
					}
				} else {
					if (fDebugEnS) {
						debug_s(indent(fIndent) + "    SKIP included file: " + is.getFilePath()
								+ " is-boundary: " + (is == boundary));
					}
				}

			}
		}

		if (fDebugEnS) {
			debug_s(indent(--fIndent) + "<-- searchUp(" + context.getFilePath() + ", " + key + ")");
		}
		return m;
	}

	private void debug_s(String str) {
		if (fDebugEnS) {
			fLog.debug(str);
		}
	}
	
	private String indent(int ind) {
		String ret = "";
		while (ind-- > 0) {
			ret += "    ";
		}
		return ret;
	}

}

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
package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ops.SVDBFindMacroOp;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.preproc.SVStringPreProcessor;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;

import org.eclipse.core.runtime.IProgressMonitor;

/**
 * This class is responsible for parsing file content when the 
 * file is not part of an existing index
 * 
 * @author ballance
 *
 */
public class SVDBShadowIndexParse implements ISVDBIndexParse {
	private SVDBIndexCollection				fSuperCollection;
	
	public SVDBShadowIndexParse(
			SVDBIndexCollection			super_collection) {
		fSuperCollection = super_collection;
	}

	public Tuple<SVDBFile, SVDBFile> parse(
			IProgressMonitor 		monitor,
			InputStream 			in, 
			String 					path, 
			List<SVDBMarker> 		markers) {
		SVPreProcessor preproc = new SVPreProcessor(path, in, null, fileMapper);
		preproc.setMacroProvider(new MacroProvider());
		
		SVPreProcOutput pp_out = preproc.preprocess();
		
		SVLanguageLevel language_level = SVLanguageLevel.computeLanguageLevel(path);
		
		SVParser parser = new SVParser();

		SVDBFile file = parser.parse(language_level, pp_out, path, markers);
		
		// Merge in markers from the pre-processor view
		for (SVDBMarker m : pp_out.getFileTree().fMarkers) {
			markers.add(m);
		}
			
		SVDBFileTree ft = pp_out.getFileTree();
		return new Tuple<SVDBFile, SVDBFile>(ft.getSVDBFile(), file);
	}
	
	@Override
	public ISVStringPreProcessor createPreProc(
			String 			path, 
			InputStream 	in,
			int 			limit_lineno) {
		SVPreProcessor preproc = new SVPreProcessor(path, in, null, fileMapper);
		MacroProvider mp = new MacroProvider();
		preproc.setMacroProvider(mp);
		
		/* SVPreProcOutput pp_out = */ preproc.preprocess();
		
		return new SVStringPreProcessor(mp);
	}

	private ISVPreProcFileMapper fileMapper = new ISVPreProcFileMapper() {
		
		public int mapFilePathToId(String path, boolean add) {
			// TODO Auto-generated method stub
			return 1;
		}
		
		public String mapFileIdToPath(int id) {
			// TODO Auto-generated method stub
			return null;
		}
	};
	
	private class MacroProvider implements IPreProcMacroProvider {
		private Map<String, SVDBMacroDef>		fMacroMap = new HashMap<String, SVDBMacroDef>();
		
		public MacroProvider() {
			setMacro("SVEDITOR", "");
		}
		
		public SVDBMacroDef findMacro(String name, int lineno) {
			
			if (fMacroMap.containsKey(name)) {
				return fMacroMap.get(name);
			}
		
			if (fSuperCollection != null) {
				// Otherwise, try a lookup in the associated collection
				SVDBMacroDef md = SVDBFindMacroOp.op(fSuperCollection, name, false);
				
				if (md != null) {
					// Cache 
					fMacroMap.put(name, md);
				}
				
				return md;
			}
	
			return null;
		}

		public void addMacro(SVDBMacroDef macro) {
			fMacroMap.remove(macro.getName());
			fMacroMap.put(macro.getName(), macro);
		}

		public void setMacro(String key, String value) {
			if (value == null) {
				fMacroMap.remove(key);
			} else {
				addMacro(new SVDBMacroDef(key, value));
			}
		}
	};
	
}

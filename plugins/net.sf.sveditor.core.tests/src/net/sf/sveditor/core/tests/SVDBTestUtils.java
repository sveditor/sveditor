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


package net.sf.sveditor.core.tests;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.InputStreamCopier;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBImportStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

public class SVDBTestUtils {

	public static void assertNoErrWarn(SVDBFile file) {
		for (ISVDBItemBase it : file.getChildren()) {
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)it;
				
				if (m.getMarkerType() == MarkerType.Error ||
						m.getMarkerType() == MarkerType.Warning) {
					System.out.println("[ERROR] ERR/WARN: " + m.getMessage() +
							" @ " + file.getName() + ":" + m.getLocation().getLine());
					TestCase.fail("Unexpected marker type " + m.getMarkerType() + " @ " + 
							file.getName() + ":" + m.getLocation().getLine());
				}
			}
		}
	}
	
	public static void assertFileHasElements(SVDBFile file, String ... elems) {
		for (String e : elems) {
			if (findElement(file, e) == null) {
				TestCase.fail("Failed to find element \"" + e + "\" in file " + file.getName());
			}
		}
	}
	
	public static void assertFileDoesNotHaveElements(SVDBFile file, String ... elems) {
		for (String e : elems) {
			if (findElement(file, e) != null) {
				TestCase.fail("Found unexpected element \"" + e + "\" in file " + file.getName());
			}
		}
	}
	
	public static ISVDBItemBase findInFile(SVDBFile file, String name) {
		return findElement(file, name);
	}
	
	private static ISVDBItemBase findElement(ISVDBScopeItem scope, String e) {
		for (ISVDBItemBase it : scope.getItems()) {
			if (SVDBItem.getName(it).equals(e)) {
				return it;
			} else if (it instanceof SVDBVarDeclStmt) {
				for (ISVDBChildItem c : ((SVDBVarDeclStmt)it).getChildren()) {
					SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
					if (vi.getName().equals(e)) {
						return vi;
					}
				}
			} else if (it.getType() == SVDBItemType.ImportStmt) {
				for (ISVDBChildItem c : ((SVDBImportStmt)it).getChildren()) {
					SVDBImportItem ii = (SVDBImportItem)c;
					if (ii.getImport().equals(e)) {
						return ii;
					}
				}
			} else if (it instanceof ISVDBScopeItem) {
				ISVDBItemBase t;
				if ((t = findElement((ISVDBScopeItem)it, e)) != null) {
					return t;
				}
			}
		}
		
		return null;
	}
	
	public static SVDBFile parse(String content, String filename) {
		return parse(content, filename, false);
	}

	public static Tuple<SVDBFile, SVDBFile> parsePreProc(String content, String filename, boolean exp_err) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> file = parse(null, new StringInputStream(content), filename, markers);
		if (!exp_err) {
			TestCase.assertEquals("Unexpected errors", 0, markers.size());
		}
		return file;
	}

	public static SVDBFile parse(String content, String filename, boolean exp_err) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = parse(null, content, filename, markers);
		if (!exp_err) {
			TestCase.assertEquals("Unexpected errors", 0, markers.size());
		}
		return file;
	}
	
	public static SVDBFile parse(
			LogHandle				log,
			String 					content, 
			String 					filename,
			List<SVDBMarker>		markers) {
		return parse(log, new StringInputStream(content), filename, markers).second();
	}
	
	public static Tuple<SVDBFile, SVDBFile> parse(
			LogHandle				log,
			InputStream				content_i, 
			String 					filename,
			List<SVDBMarker>		markers) {
		SVDBFile file = null;
		InputStreamCopier copier = new InputStreamCopier(content_i);
		InputStream content = copier.copy();
		SVPreProcScanner pp_scanner = new SVPreProcScanner();
		pp_scanner.init(content, filename);
		
		SVDBPreProcObserver pp_observer = new SVDBPreProcObserver();
		pp_scanner.setObserver(pp_observer);
		pp_scanner.scan();
		
		final SVDBFile pp_file = pp_observer.getFiles().get(0);
		IPreProcMacroProvider macro_provider = new IPreProcMacroProvider() {

			public void setMacro(String key, String value) {}
			public void addMacro(SVDBMacroDef macro) {}
			
			public SVDBMacroDef findMacro(String name, int lineno) {
				for (ISVDBItemBase it : pp_file.getChildren()) {
					if (it.getType() == SVDBItemType.MacroDef && 
							SVDBItem.getName(it).equals(name)) {
						return (SVDBMacroDef)it;
					}
				}
				return null;
			}
		};
		
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(macro_provider);
		if (log != null) {
			InputStream in = copier.copy();
			SVPreProcScanner pp = new SVPreProcScanner();
			pp.setDefineProvider(dp);
//			pp.setScanner(this);
//			pp.setObserver(this);

			pp.init(in, filename);
			pp.setExpandMacros(true);
			pp.setEvalConditionals(true);

			StringBuilder sb = new StringBuilder();
			int ch;
			while ((ch = pp.get_ch()) != -1) {
				sb.append((char)ch);
			}
			log.debug("Content:");
			log.debug(sb.toString());
		}
		
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);
		
		content = copier.copy();
		file = factory.parse(content, filename, markers);
		
		for (SVDBMarker m : markers) {
			if (log != null) {
				log.debug("[MARKER] " + m.getMessage());
			} else {
				System.out.println("[MARKER] " + m.getMessage());
			}
		}
		
		return new Tuple<SVDBFile, SVDBFile>(pp_file, file);
	}

	public static String preprocess(String content, final String filename) {
		SVPreProcScanner pp_scanner = new SVPreProcScanner();
		pp_scanner.init(new StringInputStream(content), filename);
		
		SVDBPreProcObserver pp_observer = new SVDBPreProcObserver();
		pp_scanner.setObserver(pp_observer);
		pp_scanner.scan();
		final SVDBFile pp_file = pp_observer.getFiles().get(0);
		IPreProcMacroProvider macro_provider = new IPreProcMacroProvider() {

			public void setMacro(String key, String value) {}
			public void addMacro(SVDBMacroDef macro) {}
			
			public SVDBMacroDef findMacro(String name, int lineno) {
				if (name.equals("__FILE__")) {
					return new SVDBMacroDef("__FILE__", new ArrayList<String>(), 
							"\"" + filename + "\"");
				} else if (name.equals("__LINE__")) {
					return new SVDBMacroDef("__LINE__", new ArrayList<String>(), "0");
				} else {
					for (ISVDBItemBase it : pp_file.getChildren()) {
						if (it.getType() == SVDBItemType.MacroDef && 
								SVDBItem.getName(it).equals(name)) {
							return (SVDBMacroDef)it;
						}
					}
				}
				return null;
			}
			
		};
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(macro_provider);
		pp_scanner = new SVPreProcScanner();
		pp_scanner.init(new StringInputStream(content), filename);
		pp_scanner.setExpandMacros(true);
		pp_scanner.setDefineProvider(dp);
		
		StringBuilder result = new StringBuilder();
		int c;
		while ((c = pp_scanner.get_ch()) != -1) {
			result.append((char)c);
		}
		
		return result.toString();
	}

}

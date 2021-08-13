/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.tests;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBFileFactory;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBBind;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBMacroDef;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInst;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInstItem;
import org.eclipse.hdt.sveditor.core.db.SVDBPreProcObserver;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker.MarkerType;
import org.eclipse.hdt.sveditor.core.db.index.old.InputStreamCopier;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBAssertStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBImportItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBImportStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVLanguageLevel;
import org.eclipse.hdt.sveditor.core.parser.SVParser;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcDirectiveScanner;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcOutput;
import org.eclipse.hdt.sveditor.core.preproc.SVPreProcessor;
import org.eclipse.hdt.sveditor.core.scanner.IPreProcMacroProvider;

import junit.framework.TestCase;

public class SVDBTestUtils {

	public static void assertNoErrWarn(SVDBFile file) {
		TestCase.assertNotNull(file);
		for (ISVDBItemBase it : file.getChildren()) {
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)it;
				
				if (m.getMarkerType() == MarkerType.Error ||
						m.getMarkerType() == MarkerType.Warning) {
					System.out.println("[ERROR] ERR/WARN: " + m.getMessage() +
							" @ " + file.getName() + ":" + 
							SVDBLocation.unpackLineno(m.getLocation()));
					TestCase.fail("Unexpected marker type " + m.getMarkerType() + " @ " + 
							file.getName() + ":" + 
							SVDBLocation.unpackLineno(m.getLocation()));
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
			ISVDBItemBase ret = findElement(it, e);
			if (ret != null) {
				return ret;
			}
		}
		
		return null;
	}

	private static ISVDBItemBase findElement(ISVDBItemBase it, String e) {
		if (SVDBItem.getName(it).equals(e)) {
			return it;
		} else if (it instanceof SVDBVarDeclStmt) {
			for (ISVDBChildItem c : ((SVDBVarDeclStmt)it).getChildren()) {
				SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
				if (vi.getName().equals(e)) {
					return vi;
				}
			}
		} else if (it instanceof SVDBModIfcInst) {
			for (ISVDBChildItem c : ((SVDBModIfcInst)it).getChildren()) {
				SVDBModIfcInstItem mi = (SVDBModIfcInstItem)c;
				if (mi.getName().equals(e)) {
					return mi;
				}
			}
		} else if (it.getType() == SVDBItemType.ImportStmt) {
			for (ISVDBChildItem c : ((SVDBImportStmt)it).getChildren()) {
				SVDBImportItem ii = (SVDBImportItem)c;
				if (ii.getImport().equals(e)) {
					return ii;
				}
			}
		} else if (it.getType() == SVDBItemType.AssertStmt) {
			SVDBAssertStmt asrt = (SVDBAssertStmt) it;
			if (asrt.getName().equals(e))  {
				return (asrt);
			}
		} else if (it instanceof ISVDBScopeItem) {
			ISVDBItemBase t;
			if ((t = findElement((ISVDBScopeItem)it, e)) != null) {
				return t;
			}
		} else {
			// Special-case handling
			switch (it.getType()) {
				case Bind: {
					SVDBModIfcInst inst = ((SVDBBind)it).getBindInst();
					if (inst != null) {
						return findElement(inst, e);
					}
					} break;
				default:
					break;
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
	
	public static Tuple<SVDBFile, SVDBFile> parse(LogHandle log, File file, List<SVDBMarker> markers) {
		InputStream in = null;
		try {
			in = new FileInputStream(file);
		} catch (IOException e) {
			TestCase.fail("Failed to open file \"" + file.getAbsolutePath() + "\": " + e.getMessage());
		}
		
		Tuple<SVDBFile, SVDBFile> ret = parse(log, in, file.getName(), markers);
		
		return ret;
	}

	public static SVDBFile parse(
			LogHandle 			log, 
			String 				content, 
			String 				filename, 
			boolean 			exp_err) {
		return parse(log, SVLanguageLevel.SystemVerilog, 
				content, filename, exp_err);
	}
	
	public static SVDBFile parse(
			LogHandle 			log, 
			SVLanguageLevel		language,
			String 				content, 
			String 				filename, 
			boolean 			exp_err) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = parse(log, language, content, filename, markers);
		if (!exp_err) {
			for (int i=0; i<markers.size(); i++) {
				if (markers.get(i).getMarkerType() != SVDBMarker.MarkerType.Error) {
					markers.remove(i);
					i--;
				}
			}
			TestCase.assertEquals("Unexpected errors", 0, markers.size());
		}
		return file;
	}

	public static SVDBFile parse(
			LogHandle				log,
			String 					content, 
			String 					filename,
			List<SVDBMarker>		markers) {
		return parse(log, SVLanguageLevel.SystemVerilog,
				content, filename, markers);
	}
	
	public static SVDBFile parse(
			LogHandle				log,
			SVLanguageLevel			language,
			String 					content, 
			String 					filename,
			List<SVDBMarker>		markers) {
		return parse(log, language, null,
				new StringInputStream(content), 
				filename, 
				markers).second();
	}
	
	public static Tuple<SVDBFile, SVDBFile> parse(
			LogHandle				log,
			InputStream				content_i, 
			String 					filename,
			List<SVDBMarker>		markers) {
		return parse(log, SVLanguageLevel.SystemVerilog, null,
				content_i, filename, markers);
	}
	
	public static Tuple<SVDBFile, SVDBFile> parse(
			LogHandle				log,
			SVLanguageLevel			language,
			SVParserConfig			config,
			InputStream				content_i, 
			String 					filename,
			List<SVDBMarker>		markers) {
		SVPreProcessor pp = new SVPreProcessor(filename, content_i, null, null);
		
		SVPreProcOutput pp_out = pp.preprocess();

		collectMarkers(markers, pp.getFileTree());
	
		if (log != null) {
			log.debug("Content (SVPreProc):");
			log.debug(pp_out.toString());
		}
		
		SVDBFile pp_file = pp.getFileTree().getSVDBFile();
		
		TestCase.assertNotNull(pp_file);
		
		SVParser parser = new SVParser();
		if (config != null) {
			parser.setConfig(config);
		}
		SVDBFile file = parser.parse(language, pp_out, filename, markers);
		
		TestCase.assertNotNull(file);
		
		for (SVDBMarker m : markers) {
			if (log != null) {
				log.debug("[MARKER] " + m.getMessage());
			}
		}
		
		return new Tuple<SVDBFile, SVDBFile>(pp_file, file);
	}	
	
	private static void collectMarkers(List<SVDBMarker> markers, SVDBFileTree ft) {
		markers.addAll(ft.getMarkers());
		
		for (SVDBFileTree ft_s : ft.getIncludedFileTreeList()) {
			collectMarkers(markers, ft_s);
		}
	}
	
	public static Tuple<SVDBFile, SVDBFile> parse_old(
			LogHandle				log,
			InputStream				content_i, 
			String 					filename,
			List<SVDBMarker>		markers) {
		SVDBFile file = null;
		InputStreamCopier copier = new InputStreamCopier(content_i);
		InputStream content = copier.copy();
		/*
		SVPreProcScanner pp_scanner = new SVPreProcScanner();
		pp_scanner.init(content, filename);
		 */
		SVPreProcDirectiveScanner pp_dir_scanner = new SVPreProcDirectiveScanner();
		pp_dir_scanner.init(content, filename);
		
		SVDBPreProcObserver pp_observer = new SVDBPreProcObserver();
		/*
		pp_scanner.setObserver(pp_observer);
		pp_scanner.scan();
		 */
		pp_dir_scanner.setObserver(pp_observer);
		pp_dir_scanner.process();
		
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
		
		if (log != null) {
			InputStream in = copier.copy();
			
			/*
			SVPreProcDirectiveScanner pp = new SVPreProcDirectiveScanner();
			pp.setDefineProvider(dp);

			pp.init(in, filename);

			StringBuilder sb = new StringBuilder();
			int ch;	public SVDBFile parse(
			SVLanguageLevel		language_level,
			InputStream 		in, 
			String 				filename, 
			List<SVDBMarker> 	markers) {
			while ((ch = pp.get_ch()) != -1) {
				sb.append((char)ch);
			}
			log.debug("Content:");
			log.debug(sb.toString());
		
			in = copier.copy();
			 */
			SVPreProcessor preproc = new SVPreProcessor(
					filename, in, null, null);
			preproc.setMacroProvider(macro_provider);
			
			log.debug("Content (SVPreProc):");
			log.debug(preproc.preprocess().toString());
		}
		
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(macro_provider);
		
		content = copier.copy();
		file = factory.parse(SVLanguageLevel.SystemVerilog, content, filename, markers);
		
		for (SVDBMarker m : markers) {
			if (log != null) {
				log.debug("[MARKER] " + m.getMessage());
			}
			/*
			else {
				System.out.println("[MARKER] " + m.getMessage());
			}
			 */
		}
		
		return new Tuple<SVDBFile, SVDBFile>(pp_file, file);
	}

	public static String preprocess(String content, final String filename) {
		SVPreProcDirectiveScanner pp_scanner = new SVPreProcDirectiveScanner();
		pp_scanner.init(new StringInputStream(content), filename);
		
		SVDBPreProcObserver pp_observer = new SVDBPreProcObserver();
		pp_scanner.setObserver(pp_observer);
		pp_scanner.process();
		final SVDBFile pp_file = pp_observer.getFiles().get(0);
		IPreProcMacroProvider macro_provider = new IPreProcMacroProvider() {

			public void setMacro(String key, String value) {}
			public void addMacro(SVDBMacroDef macro) {}
			
			public SVDBMacroDef findMacro(String name, int lineno) {
				if (name.equals("__FILE__")) {
					return new SVDBMacroDef("__FILE__", "\"" + filename + "\"");
				} else if (name.equals("__LINE__")) {
					return new SVDBMacroDef("__LINE__", "0");
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
//		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(macro_provider);
		/*
		pp_scanner = new SVPreProcScanner();
		pp_scanner.init(new StringInputStream(content), filename);
		pp_scanner.setExpandMacros(true);
		pp_scanner.setDefineProvider(dp);
		
		StringBuilder result = new StringBuilder();
		int c;
		while ((c = pp_scanner.get_ch()) != -1) {
			result.append((char)c);
		}
		 */
		SVPreProcessor pp = new SVPreProcessor(
				filename, 
				new StringInputStream(content), 
				null, null);
		pp.setMacroProvider(macro_provider);
		SVPreProcOutput out = pp.preprocess();
	
		return out.toString();
	}

}

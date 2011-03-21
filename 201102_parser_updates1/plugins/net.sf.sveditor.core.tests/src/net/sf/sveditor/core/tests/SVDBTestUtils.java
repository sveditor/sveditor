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

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.util.ArrayList;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

public class SVDBTestUtils {

	public static void assertNoErrWarn(SVDBFile file) {
		for (ISVDBItemBase it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)it;
				
				if (m.getName().equals(SVDBMarker.MARKER_ERR) ||
						m.getName().equals(SVDBMarker.MARKER_WARN)) {
					System.out.println("[ERROR] ERR/WARN: " + m.getMessage() +
							" @ " + file.getName() + ":" + m.getLocation().getLine());
					TestCase.fail("Unexpected " + m.getName() + " @ " + 
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
	
	public static ISVDBItemBase findInFile(SVDBFile file, String name) {
		return findElement(file, name);
	}
	
	private static ISVDBItemBase findElement(ISVDBScopeItem scope, String e) {
		for (ISVDBItemBase it : scope.getItems()) {
			if (SVDBItem.getName(it).equals(e)) {
				return it;
			} else if (it.getType() == SVDBItemType.VarDeclStmt) {
				for (SVDBVarDeclItem vi : ((SVDBVarDeclStmt)it).getVarList()) {
					if (vi.getName().equals(e)) {
						return vi;
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
		SVDBFile file = null;
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
				for (ISVDBItemBase it : pp_file.getItems()) {
					if (it.getType() == SVDBItemType.MacroDef && 
							SVDBItem.getName(it).equals(name)) {
						return (SVDBMacroDef)it;
					}
				}
				return null;
			}
			
		};
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(macro_provider);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);
		
		file = factory.parse(new StringInputStream(content), filename);
		
		// Test persistence
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		SVDBPersistenceWriter writer = new SVDBPersistenceWriter(bos);
		try {
			writer.writeSVDBItem(file);
		} catch (DBWriteException e) {
			TestCase.fail("Received DBWriteException: " + e.getMessage());
		}
		
		writer.close();
		
		SVDBPersistenceReader reader = new SVDBPersistenceReader(
				new ByteArrayInputStream(bos.toByteArray()));
		
		try {
			reader.readSVDBItem(null);
		} catch (DBFormatException e) {
			e.printStackTrace();
			TestCase.fail("Received DBFormatException: " + e.getMessage());
		}
		
		return file;
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
					for (ISVDBItemBase it : pp_file.getItems()) {
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

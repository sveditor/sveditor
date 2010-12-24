package net.sf.sveditor.core.tests;

import java.util.ArrayList;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

public class SVDBTestUtils {

	public static void assertNoErrWarn(SVDBFile file) {
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)it;
				
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR) ||
						m.getName().equals(SVDBMarkerItem.MARKER_WARN)) {
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
			if (!findElement(file, e)) {
				TestCase.fail("Failed to find element \"" + e + "\" in file " + file.getName());
			}
		}
	}
	
	private static boolean findElement(ISVDBScopeItem scope, String e) {
		for (SVDBItem it : scope.getItems()) {
			if (it.getName().equals(e)) {
				return true;
			} else if (it instanceof ISVDBScopeItem) {
				if (findElement((ISVDBScopeItem)it, e)) {
					return true;
				}
			}
		}
		
		return false;
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
			@Override
			public void setMacro(String key, String value) {}
			@Override
			public void addMacro(SVDBMacroDef macro) {}
			
			@Override
			public SVDBMacroDef findMacro(String name, int lineno) {
				for (SVDBItem it : pp_file.getItems()) {
					if (it.getType() == SVDBItemType.Macro && 
							it.getName().equals(name)) {
						return (SVDBMacroDef)it;
					}
				}
				return null;
			}
			
		};
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(macro_provider);
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(dp);
		
		file = factory.parse(new StringInputStream(content), filename);
		
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
			@Override
			public void setMacro(String key, String value) {}
			@Override
			public void addMacro(SVDBMacroDef macro) {}
			
			@Override
			public SVDBMacroDef findMacro(String name, int lineno) {
				if (name.equals("__FILE__")) {
					return new SVDBMacroDef("__FILE__", new ArrayList<String>(), 
							"\"" + filename + "\"");
				} else if (name.equals("__LINE__")) {
					return new SVDBMacroDef("__LINE__", new ArrayList<String>(), "0");
				} else {
					for (SVDBItem it : pp_file.getItems()) {
						if (it.getType() == SVDBItemType.Macro && 
								it.getName().equals(name)) {
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

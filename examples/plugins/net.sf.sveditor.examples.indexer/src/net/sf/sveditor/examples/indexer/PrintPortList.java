package net.sf.sveditor.examples.indexer;

import java.io.File;
import java.io.PrintStream;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.search.SVDBFindByTypeMatcher;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

/**
 * Example of using SVE's indexing subsystem to parse source files and 
 * print the portlist of all modules.
 * 
 * @author ballance
 *
 */
public class PrintPortList implements IApplication {

	@Override
	public Object start(IApplicationContext context) throws Exception {
		SVCorePlugin.getDefault().enableDebug(false);
		String args[] = (String[])context.getArguments().get(IApplicationContext.APPLICATION_ARGS);
		
		// Create the filelist
		File argfile = File.createTempFile("argfile", ".f");
		PrintStream ps = new PrintStream(argfile);
	
		for (String arg : args) {
			ps.println(arg);
		}
		
		ps.close();
		
		// Create an index for the files
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), 
				"GLOBAL", 						// Project - a generic string is fine
				argfile.getAbsolutePath(),		// Filelist
				SVDBArgFileIndexFactory.TYPE,	// Index type
				null);							// Config
		
		// Force the index to build
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
		
		// Get all source files
		Iterable<String> src_files = index.getFileList(
				new NullProgressMonitor(), ISVDBIndex.FILE_ATTR_SRC_FILE);
		System.out.println("Source Files:");
		for (String src_file : src_files) {
			System.out.println("  " + src_file);
		}
		
		// Find all modules
		List<SVDBDeclCacheItem> items = index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"", // name
				new SVDBFindByTypeMatcher(SVDBItemType.ModuleDecl));
		
		for (SVDBDeclCacheItem ci : items) {
			// The Cache Item is a lazily-bound reference to the AST
			// Call 'getSVDBItem' to get the actual item.
			SVDBModuleDecl module_decl = (SVDBModuleDecl)ci.getSVDBItem();

			System.out.println("Module: " + module_decl.getName());
			// A port is a variable declaration with additional info, such 
			// as direction attributes
			for (SVDBParamPortDecl port : module_decl.getPorts()) {
		
				SVDBTypeInfo datatype = port.getTypeInfo();
				for (ISVDBChildItem port_sub : port.getChildren()) {
					System.out.println("    " + getDir(port.getDir()) + " " +
							getTypeName(datatype) + 
							((SVDBVarDeclItem)port_sub).getName());
				}
			}
		}
		
		// Remove the index from the registry
		rgy.disposeIndex(index, "");
	
		// Remove the temporary filelist file
		argfile.delete();


		return Status.OK_STATUS;
	}
	
	private static String getDir(int dir) {
		if ((dir & SVDBParamPortDecl.Direction_Input) != 0) {
			return "input";
		} else if ((dir & SVDBParamPortDecl.Direction_Output) != 0) {
			return "output";
		} else if ((dir & SVDBParamPortDecl.Direction_Inout) != 0) {
			return "inout";
		} else {
			return "unknown"; // should not happen
		}
	}
	
	private static String getTypeName(SVDBTypeInfo type_info) {
		if (type_info != null) {
			return type_info + " ";
		} else {
			return "";
		}
	}

	@Override
	public void stop() {
		// TODO Auto-generated method stub

	}

}

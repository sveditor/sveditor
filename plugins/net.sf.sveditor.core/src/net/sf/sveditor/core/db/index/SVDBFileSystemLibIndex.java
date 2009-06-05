package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.fileset.SVFilesystemFileMatcher;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

public class SVDBFileSystemLibIndex extends AbstractSVDBLibIndex {
	private File					fBaseLocationFile;
	private String					fBaseLocation;
	
	public SVDBFileSystemLibIndex(
			String 			project, 
			String			base_location) {
		super(project, base_location);
		
		fBaseLocation = base_location;
		
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();
		
		String exp = null;
		try {
			exp = mgr.performStringSubstitution(base_location);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		System.out.println("exp=" + exp);
		
		fBaseLocationFile = new File(exp);
		
		SVFilesystemFileMatcher matcher = new SVFilesystemFileMatcher();
		SVFileSet fs = SVCorePlugin.getDefault().getDefaultFileSet(
				fBaseLocationFile.getParentFile().getAbsolutePath());
		matcher.addFileSet(fs);
		fFileMatchers.add(matcher);
	}
	
	public String getTypeID() {
		return SVDBLibPathIndexFactory.TYPE;
	}

	public String getBaseLocation() {
		return fBaseLocation;
	}

	@Override
	protected InputStream openStream(String path) {
		InputStream ret = null;
		
		try {
			ret = new FileInputStream(path);
		} catch(IOException e) {
			System.out.println("Failed to open path \"" + path + "\"");
			e.printStackTrace();
		}

		return ret;
	}

	@Override
	protected long getLastModifiedTime(String file) {
		File f = new File(file);
		
		return f.lastModified();
	}
}

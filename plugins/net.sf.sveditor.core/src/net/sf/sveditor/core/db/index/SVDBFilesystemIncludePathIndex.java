package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

public class SVDBFilesystemIncludePathIndex extends AbstractSVDBIndex {
	private String						fBaseLocation;
	private File						fBaseLocationDir;
	
	public SVDBFilesystemIncludePathIndex(String project, String base_location) {
		super(project);
		
		fBaseLocation = base_location;
		
		String base_location_exp = fBaseLocation;
		
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();

		try {
			base_location_exp = mgr.performStringSubstitution(base_location_exp); 
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		fBaseLocationDir = new File(base_location_exp);
	}
	
	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		File try_file = new File(fBaseLocationDir, leaf);
		
		if (try_file.exists()) {
			SVDBFile file = processPreProcFile(try_file);
			return new SVDBSearchResult<SVDBFile>(file, this);
		} else {
			return null;
		}
	}
	
	protected SVDBFile processPreProcFile(File path) {
		SVPreProcScanner 	sc = new SVPreProcScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();

		sc.setObserver(ob);
		
		// fLog.debug("processPreProcFile: path=" + path);
		// InputStream in = openStream(path);
		InputStream in = null;
		try {
			in = new FileInputStream(path);
		} catch (IOException e) { }
		
		if (in == null) {
			System.out.println("failed to open \"" + path + "\"");
		}

		sc.init(in, path.getAbsolutePath());
		sc.scan();
		
		try {
			in.close();
		} catch (IOException e) { }

		SVDBFile file = ob.getFiles().get(0);

		file.setLastModified(path.lastModified());
		
		return file;
	}


	@Override
	protected void buildIndex() {}

	@Override
	protected void buildPreProcFileMap() {}

	@Override
	protected boolean isLoadUpToDate() {
		return true;
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {}

	public String getBaseLocation() {
		return fBaseLocation;
	}

	public int getIndexType() {
		// TODO Auto-generated method stub
		return 0;
	}

	public String getTypeID() {
		// TODO Auto-generated method stub
		return null;
	}

	public void rebuildIndex() {}

	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	public SVDBFile parse(InputStream in, String path) {
		
		return null;
	}

}

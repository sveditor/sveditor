package net.sf.sveditor.core.preproc;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;

public class SVPathPreProcIncFileProvider implements ISVPreProcIncFileProvider {
	private List<String>				fIncDirs;
	private ISVDBFileSystemProvider		fFSProvider;
	
	public SVPathPreProcIncFileProvider(ISVDBFileSystemProvider fs_provider) {
		fFSProvider = fs_provider;
		fIncDirs = new ArrayList<String>();
	}
	
	public void addIncdir(String dir) {
		if (!fIncDirs.contains(dir)) {
			fIncDirs.add(dir);
		}
	}

	public Tuple<String, InputStream> findIncFile(String incfile) {
		Tuple<String, InputStream> ret = null;
		
		for (String incdir : fIncDirs) {
			String resolved_path = SVFileUtils.resolvePath(
					incfile, incdir, fFSProvider, true);
			
			if (fFSProvider.fileExists(resolved_path)) {
				InputStream in = fFSProvider.openStream(resolved_path);
				ret = new Tuple<String, InputStream>(resolved_path, in);
				break;
			}
		}

		return ret;
	}

}

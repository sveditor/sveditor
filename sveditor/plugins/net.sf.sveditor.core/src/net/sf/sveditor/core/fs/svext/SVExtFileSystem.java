package net.sf.sveditor.core.fs.svext;

import java.net.URI;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileSystem;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.project.SVDBProjectData;

public class SVExtFileSystem extends FileSystem {
	public static final String			EXT_SRC_DIRNAME = "External SV Files";
//	private WeakHashMap<SVDBProjectData, SVExtProjectFileStore>	fProjectMap;
	private Map<SVDBProjectData, SVExtProjectFileStore>	fProjectMap;

	public SVExtFileSystem() { 
		fProjectMap = new HashMap<SVDBProjectData, SVExtProjectFileStore>();
	}
	
	@Override
	public IFileStore getStore(URI uri) {
		IFileStore ret = null;
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		String pname = uri.getAuthority();
		if (pname != null) {
			IProject p = root.getProject(pname);
			if (p != null) {
				SVDBProjectData pd = SVCorePlugin.getDefault().getProjMgr().getProjectData(p);
				if (!fProjectMap.containsKey(pd)) {
					fProjectMap.put(pd, new SVExtProjectFileStore(pd));
				}

				ret = fProjectMap.get(pd);
				if (uri.getPath() != null && uri.getPath().length() > 1) {
					List<String> path_elems = SVFileUtils.splitPath(uri.getPath());
					for (String pe : path_elems) {
						IFileStore pe_s = ret.getChild(pe);
						if (pe_s == null) {
							ret = null;
							break;
						} else {
							ret = pe_s;
						}
					}
				}
			} else {
				System.out.println("Error: failed to get project for " + uri.getPath());
			}
		}
		return ret;
	}

	@Override
	public boolean canWrite() {
		return true; 
	}

	@Override
	public boolean canDelete() {
		return false;
	}

}

package net.sf.sveditor.core.db.index;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.src_collection.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;



public class SVDBIndexUtil {
	
	private static LogHandle		fLog = LogFactory.getLogHandle("SVDBIndexUtil");
	
	public static Tuple<ISVDBIndex, SVDBIndexCollectionMgr> findIndexFile(String path, String project, boolean create_shadow) {
		ISVDBIndex 				index     = null;
		SVDBIndexCollectionMgr	index_mgr = null;
		IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot();

		// Sort the project list so we check the active project's
		// index first
		List<IProject> projects = new ArrayList<IProject>();
		for (IProject p : ws_root.getProjects()) {
			if (project != null && p.getName().equals(project)) {
				projects.add(0, p);
			} else {
				projects.add(p);
			}
		}
		
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		// First, search without looking at shadow indexes
		for (IProject p : projects) {
			// Ignore projects that are closed
			if (!p.isOpen()) {
				continue;
			}
			SVDBProjectData pdata = p_mgr.getProjectData(p);
			List<SVDBSearchResult<SVDBFile>> result = pdata.getProjectIndexMgr().findPreProcFile(path, false);
			if (result.size() > 0) {
				index = result.get(0).getIndex();
				fLog.debug("File \"" + path + "\" is in index " + 
						index.getBaseLocation() + " in project " + pdata.getName());
				index_mgr = pdata.getProjectIndexMgr();
				break;
			}
		}
		
		if (index == null) {
			// Now, search shadow indexes as well
			for (IProject p : projects) {
				if (!p.isOpen()) {
					continue;
				}
				
				SVDBProjectData pdata = p_mgr.getProjectData(p);
				List<SVDBSearchResult<SVDBFile>> result = pdata.getProjectIndexMgr().findPreProcFile(path, true);
				if (result.size() > 0) {
					index = result.get(0).getIndex();
					index_mgr = pdata.getProjectIndexMgr();
					fLog.debug("File \"" + path + "\" is in existing shadow index " + 
							index.getBaseLocation() + " in project " + pdata.getName());
					break;
				}
			}
		}
		
		if (index == null) {
			// Finally, check the global shadow indexes
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			for (ISVDBIndex idx_t : rgy.getProjectIndexList(SVDBIndexRegistry.GLOBAL_PROJECT)) {
				if (idx_t.findPreProcFile(path) != null) {
					index = idx_t;
					index_mgr = rgy.getGlobalIndexMgr();
				}
			}
		}

		if (index == null && create_shadow) {
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			
			fLog.debug("Create a shadow index for \"" + path + "\"");
			if (project != null) {
				SVDBProjectData   pdata = p_mgr.getProjectData(projects.get(0));
			
				index_mgr = pdata.getProjectIndexMgr();
			} else {
				index_mgr = rgy.getGlobalIndexMgr();
				project = SVDBIndexRegistry.GLOBAL_PROJECT;
			}
			
			index = rgy.findCreateIndex(project, new File(path).getParent(),
					SVDBSourceCollectionIndexFactory.TYPE, null);
			index_mgr.addShadowIndex(index.getBaseLocation(), index);
		}
		
		if (index != null) {
			return new Tuple<ISVDBIndex, SVDBIndexCollectionMgr>(index, index_mgr);
		} else {
			return null;
		}
	}

}

package net.sf.sveditor.core.db.index;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;



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
			
			index = rgy.findCreateIndex(project,
					SVFileUtils.getPathParent(path),
					SVDBSourceCollectionIndexFactory.TYPE, null);
			index_mgr.addShadowIndex(index.getBaseLocation(), index);
		}
		
		if (index != null) {
			return new Tuple<ISVDBIndex, SVDBIndexCollectionMgr>(index, index_mgr);
		} else {
			return null;
		}
	}

	public static String expandVars(
			String 			path,
			boolean			expand_env_vars) {
		boolean workspace_prefix = path.startsWith("${workspace_loc}");
		String exp_path = path;
		
		if (workspace_prefix) {
			exp_path = exp_path.substring("${workspace_loc}".length());
		}
	
		if (expand_env_vars) {
			StringBuilder sb = new StringBuilder(exp_path);
			StringBuilder tmp = new StringBuilder();
			int idx = 0;
			
			while (idx < sb.length()) {
				if (sb.charAt(idx) == '$') {
					tmp.setLength(0);
					
					int start = idx, end;
					String key, val=null;
					idx++;
					if (sb.charAt(idx) == '{') {
						idx++;
						
						while (idx < sb.length() && sb.charAt(idx) != '}') {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						if (idx < sb.length()) {
							end = ++idx;
						} else {
							end = idx;
						}
					} else {
						while (idx < sb.length() && 
								sb.charAt(idx) != '/' && !Character.isWhitespace(sb.charAt(idx))) {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						end = (idx-1);
					}
	
					key = tmp.toString();
					if ((val = System.getenv(key)) != null) {
						sb.replace(start, end, val);
					}
				} else {
					idx++;
				}
			}
			
			exp_path = sb.toString();
		}
	
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();
		
		try {
			exp_path = mgr.performStringSubstitution(exp_path);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		
		if (workspace_prefix) {
			exp_path = "${workspace_loc}" + exp_path;
		}
		
		return exp_path;
	}

}

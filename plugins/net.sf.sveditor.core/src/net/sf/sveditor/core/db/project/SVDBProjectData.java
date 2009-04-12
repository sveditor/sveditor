package net.sf.sveditor.core.db.project;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ISVDBFileProvider;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBProjectDataFileProvider;
import net.sf.sveditor.core.SVDBWorkspaceFileManager;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexList;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

public class SVDBProjectData {
	private IPath fSVProjFilePath;
	private SVProjectFileWrapper fFileWrapper;
	private SVDBWorkspaceFileManager fFileCache;
	private SVDBIndexList fIndexList;
	private SVDBProjectDataFileProvider fFileProvider;
	private SVDBIndexList fBigIndexList;

	public SVDBProjectData(SVProjectFileWrapper wrapper, IPath projfile_path) {
		fSVProjFilePath = projfile_path;
		fFileCache = new SVDBWorkspaceFileManager();
		fIndexList = new SVDBIndexList(projfile_path.toFile());
		fBigIndexList = new SVDBIndexList(projfile_path.toFile());
		
		fBigIndexList.addIndex(fIndexList);
		fBigIndexList.addIndex(SVCorePlugin.getDefault().getBuiltinIndex());

		fFileProvider = new SVDBProjectDataFileProvider(this);

		fFileWrapper = null;
		setProjectFileWrapper(wrapper, false);
	}

	public ISVDBFileProvider getFileProvider() {
		return fFileProvider;
	}

	public SVDBWorkspaceFileManager getFileCache() {
		return fFileCache;
	}

	public ISVDBIndex getFileIndex() {
		return fBigIndexList;
	}

	public List<SVDBPath> getBuildPaths() {
		List<SVDBPath> ret = new ArrayList<SVDBPath>();

		IFile svp = ResourcesPlugin.getWorkspace().getRoot().getFile(
				fSVProjFilePath);
		
		ret.addAll(fFileWrapper.getBuildPaths());

		return ret;
	}

	public List<SVDBPath> getIncludePaths() {
		List<SVDBPath> ret = new ArrayList<SVDBPath>();

		IFile svp = ResourcesPlugin.getWorkspace().getRoot().getFile(
				fSVProjFilePath);

		ret.addAll(fFileWrapper.getIncludePaths());

		return ret;
	}

	public void refreshProjectFile() {
		try {
			IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(
					fSVProjFilePath);
			InputStream in = file.getContents();

			fFileWrapper = new SVProjectFileWrapper(in);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public SVProjectFileWrapper getProjectFileWrapper() {
		return fFileWrapper;
	}
	
	public synchronized void setProjectFileWrapper(SVProjectFileWrapper w) {
		setProjectFileWrapper(w, true);
	}

	public synchronized void setProjectFileWrapper(SVProjectFileWrapper w, boolean set_contents) {
		boolean refresh = false;
		
		if (fFileWrapper == null || !fFileWrapper.equals(w)) {
			// Need to refresh
			refresh = true;
		}
		
		fFileWrapper = w;
		
		if (set_contents) {
			try {
				IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(
						fSVProjFilePath);

				file.refreshLocal(IResource.DEPTH_ONE, null);

				ByteArrayOutputStream out = new ByteArrayOutputStream();
				fFileWrapper.toStream(out);
				
				if (file.exists()) {
					file.setContents(new ByteArrayInputStream(
							out.toByteArray()),	true, true, null);
				} else {
					file.create(new ByteArrayInputStream(
							out.toByteArray()), true, null);
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		if (refresh) {
			IWorkspaceRoot ws_r = ResourcesPlugin.getWorkspace().getRoot(); 
			IFile file = ws_r.getFile(fSVProjFilePath);
			IPath proj_path = file.getParent().getFullPath();
			
			List<SVDBPath> paths = new ArrayList<SVDBPath>();
			
			// Add an entry for this project
			paths.add(new SVDBPath("${workspace_loc}" + proj_path.toOSString(), true));
			
			// Add entries for everything currently on the build path
			for (SVDBPath path : getBuildPaths()) {
				paths.add(path);
			}
			
			// First, remove all indexes not currently on the build path
			for (int i=0; i<fIndexList.getIndexList().size(); i++) {
				boolean found = false;
				ISVDBIndex index = fIndexList.getIndexList().get(i);
				
				// If this path is 
				
				for (SVDBPath path : paths) {
					if (path.getPath().startsWith("${workspace_loc}")) {
						String project_path = path.getPath().substring("${workspace_loc}".length());
						IContainer c = ws_r.getContainerForLocation(new Path(project_path));
						
						if (c != null && c.getLocation().toFile().equals(
								index.getBaseLocation())) {
							found = true;
							break;
						}
					} else {
						if (index.getBaseLocation().equals(new File(path.getPath()))) {
							found = true;
							break;
						}
					}
				}
				
				if (!found) {
					fIndexList.removeIndex(index);
					index.dispose();
				}
			}
			
			// Next, add any indexes that aren't currently on the list
			for (int i=0; i<paths.size(); i++) {
				boolean found = false;
				SVDBPath path = paths.get(i);
				File loc;
				
				if (path.getPath().startsWith("${workspace_loc}")) {
					String project_path = path.getPath().substring("${workspace_loc}".length());
					IProject p = ws_r.getProject(project_path);
					
					if (p == null) {
						System.out.println("[ERROR] cannot locate file for path \"" + project_path + "\"");
						loc = null;
					} else {
						loc = p.getLocation().toFile();
					}
				} else {
					loc = new File(path.getPath());
				}
				
				for (ISVDBIndex index : fIndexList.getIndexList()) {
					if (index.getBaseLocation().equals(loc)) {
						found = true;
					}
				}
				
				if (!found) {
					ISVDBIndex index = null;
					
					if (path.getPath().startsWith("${workspace_loc}")) {
						try {
							Path tp = new Path(path.getPath());
							IContainer c = null;
							
							for (IProject p : ws_r.getProjects()) {
								if (p.getFullPath().equals(tp)) {
									c = p;
									break;
								}
							}
						
							if (c != null) {
								SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
								
								index = rgy.findCreateIndex(
										c.getLocation().toFile().getPath(), 
										ISVDBIndexFactory.TYPE_WorkspaceIndex);
							}
						} catch (Exception e) {
							e.printStackTrace();
						}
					} else {
						if (!loc.isDirectory()) {
							System.out.println("[WARNING] build path \"" + loc + "\" doesn't exist");
						} else {
							SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
							
							index = rgy.findCreateIndex(loc.getPath(), 
									ISVDBIndexFactory.TYPE_FilesystemIndex); 
						}
					}
					
					if (index != null) {
						fIndexList.addIndex(index);
					}
				}
			}
		}
	}

	public void refreshProjectData() {
		System.out.println("[TODO] refreshProjectData()");
	}
}

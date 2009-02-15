package net.sf.sveditor.core.db.project;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ISVDBFileProvider;
import net.sf.sveditor.core.ISVDBIndex;
import net.sf.sveditor.core.SVDBFilesystemIndex;
import net.sf.sveditor.core.SVDBIndexList;
import net.sf.sveditor.core.SVDBProjectDataFileProvider;
import net.sf.sveditor.core.SVDBWorkspaceFileManager;
import net.sf.sveditor.core.SVDBWorkspaceIndex;
import net.sf.sveditor.core.SVProjectFileWrapper;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

public class SVDBProjectData {
	private IPath fSVProjFilePath;
	private SVProjectFileWrapper fFileWrapper;
	private SVDBWorkspaceFileManager fFileCache;
	private SVDBIndexList fIndexList;
	private SVDBProjectDataFileProvider fFileProvider;

	public SVDBProjectData(SVProjectFileWrapper wrapper, IPath projfile_path) {
		fSVProjFilePath = projfile_path;
		fFileCache = new SVDBWorkspaceFileManager();
		fIndexList = new SVDBIndexList(projfile_path.toFile());

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
		return fIndexList;
	}

	public List<SVDBPath> getBuildPaths() {
		List<SVDBPath> ret = new ArrayList<SVDBPath>();

		IFile svp = ResourcesPlugin.getWorkspace().getRoot().getFile(
				fSVProjFilePath);
		if (svp != null) {
			try {
				if (svp.getProject() != null) {
					// Add build-path entries for each referenced project
					for (IProject p : svp.getProject().getReferencedProjects()) {
						// TODO: should probably just reference the SVProject
						// data for the referenced project if it exists
						SVDBPath path = new SVDBPath(p.getLocation().toFile()
								.getAbsolutePath(), false);
						ret.add(path);
					}
				}
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}

		ret.addAll(fFileWrapper.getBuildPaths());

		return ret;
	}

	public List<SVDBPath> getIncludePaths() {
		List<SVDBPath> ret = new ArrayList<SVDBPath>();

		IFile svp = ResourcesPlugin.getWorkspace().getRoot().getFile(
				fSVProjFilePath);
		if (svp != null) {
			try {
				if (svp.getProject() != null) {
					// Add build-path entries for each referenced project
					for (IProject p : svp.getProject().getReferencedProjects()) {
						// TODO: should probably just reference the SVProject
						// data for the referenced project if it exists
						SVDBPath path = new SVDBPath(p.getLocation().toFile()
								.getAbsolutePath(), false);
						ret.add(path);
					}
				}
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}

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

				file.setContents(new ByteArrayInputStream(out.toByteArray()), 
						true, true, null);
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
			paths.add(new SVDBPath(proj_path.toOSString(), true));
			
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
					if (path.isWSRelPath()) {
						IContainer c = ws_r.getContainerForLocation(new Path(path.getPath()));
						// IFile f_t = ws_r.getFile(new Path(path.getPath()));
						
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
					System.out.println("remove index \"" + index.getBaseLocation() + "\"");
					fIndexList.removeIndex(index);
					index.dispose();
				}
			}
			
			// Next, add any indexes that aren't currently on the list
			for (int i=0; i<paths.size(); i++) {
				boolean found = false;
				SVDBPath path = paths.get(i);
				File loc;
				
				if (path.isWSRelPath()) {
					IProject p = ws_r.getProject(path.getPath());
					
					if (p == null) {
						System.out.println("[ERROR] cannot locate file for path \"" + path.getPath() + "\"");
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
					System.out.println("add index \"" + loc + "\"");
					
					if (path.isWSRelPath()) {
						try {
							Path tp = new Path(path.getPath());
							IContainer c = null;
							
							for (IProject p : ws_r.getProjects()) {
								if (p.getFullPath().equals(tp)) {
									System.out.println("found project w/path");
									c = p;
									break;
								}
							}
						
							if (c != null) {
								index = new SVDBWorkspaceIndex(
										c.getLocation(), 
										ISVDBIndex.IT_BuildPath);
							} else {
								System.out.println("Path \"" + path.getPath() + 
									"\" does not exist in the workspace");
							}
						} catch (Exception e) {
							e.printStackTrace();
						}
					} else {
						if (!loc.isDirectory()) {
							System.out.println("[WARNING] build path \"" + loc + "\" doesn't exist");
						} else {
							index = new SVDBFilesystemIndex(loc, ISVDBIndex.IT_BuildPath);
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

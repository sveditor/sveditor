package net.sf.sveditor.core.db.project;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import net.sf.sveditor.core.ISVDBIndex;
import net.sf.sveditor.core.SVDBFilesystemIndex;
import net.sf.sveditor.core.SVDBIndexList;
import net.sf.sveditor.core.SVDBWorkspaceFileManager;
import net.sf.sveditor.core.SVDBWorkspaceIndex;
import net.sf.sveditor.core.SVProjectFileWrapper;

public class SVDBProjectData {
	private IPath								fSVProjFilePath;
	private SVProjectFileWrapper				fFileWrapper;
	private SVDBWorkspaceFileManager			fFileCache;
	private SVDBIndexList						fIndexList;
	
	public SVDBProjectData(
			SVProjectFileWrapper 	wrapper,
			IPath					projfile_path) {
		fSVProjFilePath = projfile_path;
		fFileWrapper = wrapper;
		fFileCache   = new SVDBWorkspaceFileManager();
		fIndexList   = new SVDBIndexList(projfile_path.toFile());
		
		for (SVDBPath path : getBuildPaths()) {
			ISVDBIndex idx = null;
			
			if (path.isWSRelPath()) {
				idx = new SVDBWorkspaceIndex(new Path(path.getPath()));
			} else {
				File f = new File(path.getPath());
				
				if (!f.isDirectory()) {
					System.out.println("path \"" + f + "\" doesn't exist");
				} else {
					idx = new SVDBFilesystemIndex(f);
				}
			}
			
			if (idx != null) {
				fIndexList.addIndex(idx);
			}
		}
	}
	
	public SVDBWorkspaceFileManager getFileCache() {
		return fFileCache;
	}
	
	public ISVDBIndex getFileIndex() {
		return fIndexList;
	}
	
	public List<SVDBPath> getBuildPaths() {
		List<SVDBPath> ret = new ArrayList<SVDBPath>();
		
		IFile svp = ResourcesPlugin.getWorkspace().getRoot().getFile(fSVProjFilePath);
		if (svp != null) {
			try {
				if (svp.getProject() != null) {
					// Add build-path entries for each referenced project
					for (IProject p : svp.getProject().getReferencedProjects()) {
						// TODO: should probably just reference the SVProject
						// data for the referenced project if it exists
						SVDBPath path = new SVDBPath(
								p.getLocation().toFile().getAbsolutePath(), 
								false);
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
		
		IFile svp = ResourcesPlugin.getWorkspace().getRoot().getFile(fSVProjFilePath);
		if (svp != null) {
			try {
				if (svp.getProject() != null) {
					// Add build-path entries for each referenced project
					for (IProject p : svp.getProject().getReferencedProjects()) {
						// TODO: should probably just reference the SVProject
						// data for the referenced project if it exists
						SVDBPath path = new SVDBPath(
								p.getLocation().toFile().getAbsolutePath(), 
								false);
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
			IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(fSVProjFilePath);
			InputStream in = file.getContents();
			
			fFileWrapper = new SVProjectFileWrapper(in);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public SVProjectFileWrapper getProjectFileWrapper() {
		 return fFileWrapper;
	}
	
	public void setProjectFileWrapper(SVProjectFileWrapper w) {
		fFileWrapper = w;
		
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
	
	public void refreshProjectData() {
		System.out.println("[TODO] refreshProjectData()");
	}
}

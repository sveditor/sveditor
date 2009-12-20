package net.sf.sveditor.core.db.project;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIncludePathIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.index.src_collection.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;

public class SVDBProjectData {
	private IPath 							fSVProjFilePath;
	private SVProjectFileWrapper 			fFileWrapper;
	private SVDBIndexCollectionMgr			fIndexCollection;
	private String							fProjectName;
	private LogHandle						fLog;

	public SVDBProjectData(
			String						project_name,
			SVProjectFileWrapper 		wrapper, 
			IPath 						projfile_path) {
		fLog = LogFactory.getDefault().getLogHandle("SVDBProjectData");
		fProjectName    = project_name;
		fSVProjFilePath = projfile_path;
		
		fIndexCollection = new SVDBIndexCollectionMgr(project_name);
		
		fFileWrapper = null;
		setProjectFileWrapper(wrapper, false);
	}

	public synchronized SVDBIndexCollectionMgr getProjectIndexMgr() {
		if (fIndexCollection == null) {
			fIndexCollection = createProjectIndex();
		}
		
		return fIndexCollection;
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
			fLog.debug("need to refresh");
			refresh = true;
		} else {
			fLog.debug("no need to refresh");
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
		
		if (refresh && fIndexCollection != null) {
			setProjectPaths(fIndexCollection, fFileWrapper);
		}
	}
	
	/**
	 * Creates the index for the project based on the paths registered
	 * in the project data
	 * 
	 * @return
	 */
	private SVDBIndexCollectionMgr createProjectIndex() {
		SVDBIndexCollectionMgr ret = new SVDBIndexCollectionMgr(fProjectName);
		SVProjectFileWrapper fw = getProjectFileWrapper();
		
		setProjectPaths(ret, fw);

		return ret;
	}
	
	private void setProjectPaths(
			SVDBIndexCollectionMgr 		sc,
			SVProjectFileWrapper		fw) {
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		sc.clear();

		// Add enabled plugin paths
		for (SVDBPath path : fw.getPluginPaths()) {
			ISVDBIndex index = rgy.findCreateIndex(
				"GLOBAL", path.getPath(), 
				SVDBPluginLibIndexFactory.TYPE, null);
			
			if (index != null) {
				sc.addPluginLibrary(index);
			} else {
				fLog.error(
						"failed to create library index \"" +
						path.getPath() + "\"");
			}
		}
		
		for (SVDBPath path : fw.getIncludePaths()) {
			ISVDBIndex index = rgy.findCreateIndex(
					fProjectName, path.getPath(), 
					SVDBIncludePathIndexFactory.TYPE, null);
			
			if (index != null) {
				sc.addIncludePath(index);
			} else {
				fLog.error(
						"failed to create include index \"" +
						path.getPath() + "\"");
			}
		}

		for (SVDBPath path : fw.getLibraryPaths()) {
			ISVDBIndex index = rgy.findCreateIndex(
					fProjectName, path.getPath(), 
					SVDBLibPathIndexFactory.TYPE, null);
			
			if (index != null) {
				sc.addLibraryPath(index);
			} else {
				fLog.error(
						"failed to create library index \"" +
						path.getPath() + "\"");
			}
		}
		
		for (SVDBPath path : fw.getArgFilePaths()) {
			ISVDBIndex index = rgy.findCreateIndex(
					fProjectName, path.getPath(),
					SVDBArgFileIndexFactory.TYPE, null);
			
			if (index != null) {
				sc.addLibraryPath(index);
			} else {
				fLog.error(
						"failed to create arg-file index \"" +
						path.getPath() + "\"");
			}
		}
		
		for (SVDBSourceCollection srcc : fw.getSourceCollections()) {
			Map<String, Object> params = new HashMap<String, Object>();

			/*
			FileSet fs = new FileSet();
			params.put(SVDBSourceCollectionIndexFactory.FILESET, fs);
			 */
			ISVDBIndex index = rgy.findCreateIndex(
					fProjectName, srcc.getBaseLocation(),
					SVDBSourceCollectionIndexFactory.TYPE, params);
			
			if (index != null) {
				sc.addSourceCollection(index);
			} else {
				fLog.error(
						"failed to create source-collection index " +
						"\"" + srcc.getBaseLocation() + "\"");
			}
		}
	}
}

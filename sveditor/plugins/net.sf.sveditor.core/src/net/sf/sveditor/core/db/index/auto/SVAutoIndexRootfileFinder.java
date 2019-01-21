package net.sf.sveditor.core.db.index.auto;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

import net.sf.sveditor.core.IFileExtProvider;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;

public class SVAutoIndexRootfileFinder {
	private ISVDBFileSystemProvider		fFileSystemProvider;
	private IFileExtProvider			fExtProvider;
	private Result						fResult;
	private IProgressMonitor			fMonitor;
	
	public static class Result {
		public Set<String>			fFilePaths;
		public Set<String>			fDirPaths;
		
		public Result() {
			fFilePaths = new HashSet<String>();
			fDirPaths = new HashSet<String>();
		}
	}
	
	public SVAutoIndexRootfileFinder(
			ISVDBFileSystemProvider			fs_provider,
			IFileExtProvider 				ext_provider) {
		fFileSystemProvider = fs_provider;
		fExtProvider = ext_provider;
	}

	public Result find(IProgressMonitor monitor, String root) {
		fMonitor = monitor;
		fResult = new Result();
		
		if (fFileSystemProvider.isDir(root)) {
			System.out.println("isDir: " + root);
			// recurse
			process_dir(root);
		} else {
			System.out.println("NotDir: " + root);
			// We've been passed a file, not a directory
			// Consider this an error for now and bail
		}
		
		fMonitor.done();
	
		return fResult;
	}
	
	private void process_dir(String path) {
		boolean added = false;
		
		fMonitor.subTask("Processing " + path);
		
		for (String child : fFileSystemProvider.getFiles(path)) {
			String ext = SVFileUtils.getPathExt(child);
			
			if (fFileSystemProvider.isDir(child)) {
				process_dir(child);
			} else {
				if (fExtProvider.getSVRootFileExts().contains(ext) ||
						fExtProvider.getVLRootFileExts().contains(ext)) {
					System.out.println("Add: " + child);
					fResult.fFilePaths.add(child);
					added = true;
				}
			}
		}
	
		if (added) {
			fResult.fDirPaths.add(path);
		}
	}
}

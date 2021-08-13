/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.net.URI;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.SVMarkers;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class SVDBWSFileSystemProvider implements ISVDBFileSystemProvider, 
		IResourceChangeListener, IResourceDeltaVisitor {

	private IWorkspaceRoot											fRoot;
	private boolean													fListenerAdded;
	private List<Reference<ISVDBFileSystemChangeListener>>			fChangeListeners;
	private LogHandle												fLog;
	
	public SVDBWSFileSystemProvider() {
		fChangeListeners = new ArrayList<Reference<ISVDBFileSystemChangeListener>>();
		fLog = LogFactory.getLogHandle("SVDBWSFileSystemProvider");
	}
	
	public void init(String path) {
		IFile 		file;
		IContainer 	folder = null;
		IWorkspaceRoot root = null;
		boolean is_ws_path = false;
		
		try {
			root = ResourcesPlugin.getWorkspace().getRoot();
		} catch (IllegalStateException e) {
			// workspace isn't open
		}
		
		fRoot = root;
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			is_ws_path = true;
		}
		
		try {
			if (is_ws_path) {
				folder = root.getFolder(new Path(path));

				if (!folder.exists()) {
					file = root.getFile(new Path(path));
					folder = file.getParent();

					if (!folder.exists()) {
						folder = null;
					}
				}
			}
		} catch (IllegalArgumentException e) {} // Happens when the folder is a project
		
		if (folder == null && root != null) {
			// Try looking at open projects
			String pname = path;
			
			if (pname.startsWith("/")) {
				pname = pname.substring(1);
			}
			if (pname.endsWith("/")) {
				pname = pname.substring(0, pname.length()-1);
			}
			
			for (IProject p_t : root.getProjects()) {
				if (p_t.isOpen() && p_t.getName().equals(pname)) {
					folder = p_t;
				}
			}
		}
	
		/** MSB: Don't refresh here
		if (folder != null) {
			try {
				folder.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) { }
		}
		 */

	}

	public void addMarker(
			String 					path,
			final String			type,
			final int				lineno,
			final String			msg) {
		if (path.startsWith("${workspace_loc}")) {
			IResource target = null;
			path = path.substring("${workspace_loc}".length());
		
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
			try {
				target = root.getFile(new Path(path));
				if (!target.exists()) {
					target = null;
				}
			} catch (IllegalArgumentException e) {}

			if (target == null) {
				try {
					target = root.getFolder(new Path(path));
				} catch (IllegalArgumentException e) {
					// Likely because the path is a project-only path (eg /a)
					// e.printStackTrace();
				}
			}
		
			if (target == null) {
				// Try project
				try {
					if (path.startsWith("/")) {
						path = path.substring(1);
					}
					target = root.getProject(path);
				} catch (IllegalArgumentException e) {}
			}

			int severity;
			String marker_type = SVMarkers.TYPE_PROBLEM;
			if (type.equals(MARKER_TYPE_ERROR)) {
				severity = IMarker.SEVERITY_ERROR;
			} else if (type.equals(MARKER_TYPE_WARNING)) {
				severity = IMarker.SEVERITY_WARNING;
			} else if (type.equals(MARKER_TYPE_TASK)) {
				severity = IMarker.SEVERITY_INFO;
				marker_type = SVMarkers.TYPE_TASK;
			} else {
				severity = IMarker.SEVERITY_INFO;
			}

			/*
			if (target != null) {
				SVCorePlugin.getDefault().propagateMarker(target, severity, lineno, msg);
			}
			 */
			try {
				IMarker marker = target.createMarker(marker_type);
				marker.setAttribute(IMarker.SEVERITY, severity);
				marker.setAttribute(IMarker.LINE_NUMBER, lineno);
				marker.setAttribute(IMarker.MESSAGE, msg);
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}
	}

	public void clearMarkers(String path) {
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = root.getFile(new Path(path));
			
			if (file.exists()) {
				try {
					file.deleteMarkers(SVMarkers.TYPE_PROBLEM, true, IResource.DEPTH_INFINITE);
					file.deleteMarkers(SVMarkers.TYPE_TASK, true, IResource.DEPTH_INFINITE);
				} catch (CoreException e) {
					// e.printStackTrace();
				}
			}
		}
	}

	public void dispose() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);		
	}
	
	public boolean fileExists(String path) {
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
			try {
				IFile file = root.getFile(new Path(path));
				IFolder folder = root.getFolder(new Path(path));

				return (file.exists() || folder.exists());
			} catch (IllegalArgumentException e) {
				return false;
			}
		} else {
			// Also look at the filesystem
			return new File(path).exists();
		}
	}

	public boolean isDir(String path) {
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			
			if (path.startsWith("/")) {
				path = path.substring(1);
			}
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
			try {
				IFolder folder = root.getFolder(new Path(path));

				return folder.exists();
			} catch (IllegalArgumentException e) {
				// Likely because the path is a project-only path (eg /a)
				// e.printStackTrace();
			}
			
			// Try project
			try {
				IProject project = root.getProject(path);
				return project.exists();
			} catch (IllegalArgumentException e) {}
			
			return false;
		} else {
			// Also look at the filesystem
			return new File(path).isDirectory();
		}
	}
	
	public List<String> getFiles(String path) {
		List<String> ret = new ArrayList<String>();
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			
			if (path.startsWith("/")) {
				path = path.substring(1);
			}
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IContainer c = null;
			
			try {
				c = root.getFolder(new Path(path));
			} catch (IllegalArgumentException e) {
				// Likely because the path is a project-only path (eg /a)
				// e.printStackTrace();
			}
			
			// Try project
			if (c == null) {
				try {
					c = root.getProject(path);
				} catch (IllegalArgumentException e) {}
			}
			
			if (c != null) {
				try {
					for (IResource m : c.members()) {
						IPath p = m.getFullPath();
						ret.add("${workspace_loc}" + p.toString());
					}
				} catch (CoreException e) { }
			}
		} else {
			File p = new File(path);
			
			if (p.isDirectory()) {
				File f_l[] = p.listFiles();
				if (f_l != null) {
					for (File f : p.listFiles()) {
						if (!f.getName().equals(".") && !f.getName().equals("..")) {
							ret.add(f.getAbsolutePath());
						}
					}
				}
			}
		}
		
		return ret;
	}

	public void closeStream(InputStream in) {
		try {
			if (in != null) {
				in.close();
			}
		} catch (IOException e) { 
			e.printStackTrace();
		}
	}
	
	public void closeStream(OutputStream out) {
		try {
			if (out != null) {
				out.close();
			}
		} catch (IOException e) {
		}
	}

	public InputStream openStream(String path) {
		InputStream ret = null;
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

			try {
				IFile file = root.getFile(new Path(path));
				if (!file.exists()) {
					return null;
				}

				for (int i=0; i<2; i++) {
					try {
						ret = file.getContents();
						break;
					} catch (CoreException e) {
						// Often times, we can just refresh the resource to avoid
						// an indexing failure
						if (i == 0 && e.getMessage().contains("out of sync")) {
							try {
								file.getParent().refreshLocal(IResource.DEPTH_INFINITE, null);
							} catch (CoreException e2) {}
						} else {
							e.printStackTrace();
						}
					}
				}
			} catch (IllegalArgumentException e) {
				// Ensure this doesn't propagate up
//				fLog.error("Badly-formed path: " + path, e);
			}
		} else {
			try {
				ret = new FileInputStream(path);
			} catch (IOException e) {}
		}
		
		return ret;
	}

	public OutputStream openStreamWrite(String path) {
		OutputStream ret = null;
		
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

			try {
				IFile file = root.getFile(new Path(path));
				ret = new SVDBWSFileSystemOutputStream(file);
			} catch (IllegalArgumentException e) {
				// Ensure this doesn't propagate up
//				fLog.error("Badly-formed path: " + path, e);
			}
		} else {
			try {
				ret = new FileOutputStream(path);
			} catch (IOException e) {}
		}
		
		return ret;
	}
	
	public String resolvePath(String path, String fmt) {
		boolean ws_path = path.startsWith("${workspace_loc}");
		
		fLog.debug("--> resolvePath path=" + path + " fmt=" + fmt);

		if (ws_path) {
			// Trim workspace_loc off so we can recognize when we've reached the root
			path = path.substring("${workspace_loc}".length());
			StringBuilder ret = new StringBuilder();

			int i=path.length()-1;
			int end;
			int skipCnt = 0;

			while (i >= 0) {
				// scan backwards find the next path element
				end = ret.length();

				while (i>=0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
					ret.append(path.charAt(i));
					i--;
				}

				if (i != -1) {
					ret.append("/");
					i--;
				}

				if ((ret.length() - end) > 0) {
					String str = ret.substring(end, ret.length()-1);
					if (str.equals("..")) {
						skipCnt++;
						// remove .. element
						ret.setLength(end);
					} else if (skipCnt > 0) {
						ret.setLength(end);
						skipCnt--;
					}
				}
			}

			if (skipCnt > 0) {
				throw new RuntimeException("exceeded skipCnt");
			}
			path = ret.reverse().toString();
		}
		
		if (fmt != null) {
			if (fmt.equals(ISVDBFileSystemProvider.PATHFMT_FILESYSTEM)) {
				if (ws_path) {
					// Map to a filesystem location
					if (isDir("${workspace_loc}" + path)) {
						IContainer c = SVFileUtils.getWorkspaceFolder(path);
						if (c != null) {
							path = c.getLocation().toOSString();
						}
					} else {
						IFile f = SVFileUtils.getWorkspaceFile(path);
						if (f != null) {
							if (f.getLocation() != null) {
								path = f.getLocation().toOSString();
							} else {
								URI uri = f.getLocationURI();
								if (uri.getScheme().equals("svext")) {
									path = uri.getPath();
									if (SVFileUtils.isWin()) {
										// Try to map the path back to a drive letter
										if (path.length() >= 3 && 
												path.charAt(0) == '/' &&
												Character.isAlphabetic(path.charAt(1)) &&
												path.charAt(2) == '/') {
											path = path.charAt(1) + ":" + path.substring(2);
										}
									}
								} else if (uri.getScheme().equals("file")) {
									if (uri.getScheme().equals("file")) {
										if (SVFileUtils.isWin() && uri.getAuthority().length() == 1) {
											path = uri.getAuthority() + ":" + uri.getPath();
										} else {
											path = uri.getAuthority() + uri.getPath();
										}
									}
								} else {
									System.out.println("Error: unknown uri scheme - " + uri);
								}
							}
						}
					}
				}
			} else if (fmt.equals(ISVDBFileSystemProvider.PATHFMT_WORKSPACE)) {
				if (!ws_path) {
					// See if we can map to a workspace location
					
					if (isDir(path)) {
						IContainer c = SVFileUtils.findWorkspaceFolder(path);
						if (c != null) {
							path = "${workspace_loc}" + c.getFullPath();
						}
					} else {
						IFile f = SVFileUtils.findWorkspaceFile(path);
						if (f != null) {
							path = "${workspace_loc}" + f.getFullPath();
						}
					}
				}
			}
		} else {
			if (ws_path) {
				path = "${workspace_loc}" + path;
			}
		}
	
		// Ensure we properly use forward slashes
		path = SVFileUtils.normalize(path);
		
		fLog.debug("<-- resolvePath path=" + path + " fmt=" + fmt);
		return path;
	}
	
	protected String normalizePath(String path) {
		StringBuilder ret = new StringBuilder();
		
		int i=path.length()-1;
		int end;
		int skipCnt = 0;
		
		while (i >= 0) {
			// scan backwards find the next path element
			end = ret.length();
			
			while (i>=0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
				ret.append(path.charAt(i));
				i--;
			}
			
			if (i != -1) {
				ret.append("/");
				i--;
			}

			if ((ret.length() - end) > 0) {
				String str = ret.substring(end, ret.length()-1);
				if (str.equals("..")) {
					skipCnt++;
					// remove .. element
					ret.setLength(end);
				} else if (skipCnt > 0) {
					ret.setLength(end);
					skipCnt--;
				}
			}
		}
		
		if (skipCnt > 0) {
			throw new RuntimeException("exceeded skipCnt");
		}
		
		return ret.reverse().toString();
	}
	

	public long getLastModifiedTime(String path) {
		if (path.startsWith("${workspace_loc}")) {
			path = path.substring("${workspace_loc}".length());
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = root.getFile(new Path(path));
			
			if (file != null && file.getLocation() != null &&
					file.getLocation().toFile() != null) {
				return file.getLocation().toFile().lastModified();
				// return file.getModificationStamp();
			} else {
				return 0;
			}
		} else {
			return new File(path).lastModified();
		}
	}

	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		synchronized (fChangeListeners) {
			if (!fListenerAdded && fRoot != null) {
				ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
				fListenerAdded = true;
			}
			fChangeListeners.add(new WeakReference<ISVDBFileSystemChangeListener>(l));
		}
	}

	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		synchronized (fChangeListeners) {
			for (int i=0; i<fChangeListeners.size(); i++) {
				ISVDBFileSystemChangeListener ll = fChangeListeners.get(i).get();
				
				if (ll == null || ll == l) {
					fChangeListeners.remove(i);
					i--;
				}
			}
		}
	}

	public synchronized boolean visit(IResourceDelta delta) throws CoreException {
		
		if (delta.getResource() instanceof IFile) {
			String file = "${workspace_loc}";
			
			file += SVFileUtils.normalize(((IFile)delta.getResource()).getFullPath().toOSString());
			
			if (delta.getKind() == IResourceDelta.REMOVED) {
				// remove from the queue (if present) and the index
				synchronized (fChangeListeners) {
					for (int i=0; i<fChangeListeners.size(); i++) {
						ISVDBFileSystemChangeListener l = fChangeListeners.get(i).get();
						if (l == null) {
							fChangeListeners.remove(i);
							i--;
						} else {
							l.fileRemoved(file);
						}
					}
				}
			} else if (delta.getKind() == IResourceDelta.ADDED) {
				synchronized (fChangeListeners) {
					for (int i=0; i<fChangeListeners.size(); i++) {
						ISVDBFileSystemChangeListener l = fChangeListeners.get(i).get();
						if (l == null) {
							fChangeListeners.remove(i);
							i--;
						} else {
							l.fileAdded(file);
						}
					}
				}				
			} else if (delta.getKind() == IResourceDelta.CHANGED) {
				if ((delta.getFlags() & IResourceDelta.CONTENT) != 0) {
					synchronized (fChangeListeners) {
						for (int i=0; i<fChangeListeners.size(); i++) {
							ISVDBFileSystemChangeListener l = fChangeListeners.get(i).get();
							if (l == null) {
								fChangeListeners.remove(i);
								i--;
							} else {
								l.fileChanged(file);
							}
						}
					}
				}
			}
		}

		return true;
	}

	public void resourceChanged(IResourceChangeEvent event) {
		try {
			if (event.getDelta() != null) {
				event.getDelta().accept(this);
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
	
}

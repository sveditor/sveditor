/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index.cache;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.DataInput;
import java.io.DataInputStream;
import java.io.DataOutput;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.RandomAccessFile;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.job_mgr.IJob;
import net.sf.sveditor.core.job_mgr.IJobMgr;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBDirFS implements ISVDBFS, ILogLevelListener {
	private File				fDBDir;
	private boolean				fAsyncClear = false;
	private boolean				fDebugEn;
	private LogHandle			fLog;
	private Set<String>			fCachePaths;
	
	public SVDBDirFS(File root) {
		fDBDir = root;
		fLog = LogFactory.getLogHandle("SVDBDirFS");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
		fCachePaths = new HashSet<String>();
		
		// Load up the current file list
		if (fDBDir.isDirectory()) {
			loadDBPaths(fDBDir);
		}
	}
	
	public void setEnableAsyncClear(boolean en) {
		fAsyncClear = en;
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	public String getRoot() {
		return fDBDir.getAbsolutePath();
	}
	
	public void removeStoragePath(List<File> db_file_list) {
		db_file_list.remove(fDBDir);
	}

	public InputStream openFileRead(String path) {
		InputStream ret = null;
		try {
			ret = new FileInputStream(new File(fDBDir, path));
			// ret = new MappedByteBufferInputStream(new File(fDBDir, path));
		} catch (IOException e) {}
		
		return ret;
	}
	
	public RandomAccessFile openChannelRead(String path) {
		RandomAccessFile ret = null;
		File target = new File(fDBDir, path);
		
		try {
			ret = new RandomAccessFile(target, "r");
		} catch (IOException e) {}
		
		return ret;
	}
	
	
	public DataInput openDataInput(String path) {
		InputStream in = openFileRead(path);
		if (in != null) {
			BufferedInputStream bin = new BufferedInputStream(in, 1024*8);
			DataInputStream din = new DataInputStream(bin);
			return din;
		} else {
			return null;
		}
	}

	public void closeInput(DataInput in) {
		try {
			if (in instanceof DataInputStream) {
				((DataInputStream)in).close();
			}
		} catch (IOException e) {}
	}

	public void closeChannel(RandomAccessFile ch) {
		try {
			ch.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public OutputStream openFileWrite(String path) {
		OutputStream ret = null;
		
		if (!fDBDir.exists()) {
			fDBDir.mkdirs();
		}

		try {
			ret = new FileOutputStream(new File(fDBDir, path));
		} catch (IOException e) {}
		
		return ret;
	}
	
	public RandomAccessFile openChannelWrite(String path) {
		RandomAccessFile ret = null;
		File target = new File(fDBDir, path);
		File target_p = target.getParentFile();
		
		if (!target_p.exists()) {
			target_p.mkdirs();
		}
		
		try {
			ret = new RandomAccessFile(new File(fDBDir, path), "rw");
			ret.setLength(0);
		} catch (IOException e) {}
		
		return ret;
	}

	public DataOutput openDataOutput(String path) {
		OutputStream out = openFileWrite(path);
		if (out != null) {
			BufferedOutputStream bos = new BufferedOutputStream(out, 1024*8);
			DataOutputStream dos = new DataOutputStream(bos);
			return dos;
		} else {
			return null;
		}
	}

	public void closeOutput(DataOutput out) {
		try {
			if (out instanceof DataOutputStream) {
				((DataOutputStream)out).close();
			}
		} catch (IOException e) {}
	}

	public void close(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {}
	}

	public boolean fileExists(String path) {
		File file = new File(fDBDir, path);
		/*
		return fCachePaths.contains(file.getAbsolutePath());
		 */
		if (file.exists()) {
			return true;
		} else {
			return false;
		}
	}
	
	public long lastModified(String path) {
		File file = new File(fDBDir, path);
		
		return file.lastModified();
	}
	
	public void delete(IProgressMonitor monitor, String path) {
		monitor.beginTask("delete", 1);
		if (path.equals("")) {
			if (fDBDir.exists()) {
				if (fAsyncClear) {
					async_clear(fDBDir);
					monitor.worked(1);
				} else {
					delete_tree(new SubProgressMonitor(monitor, 1), fDBDir);
				}
			}
			// Empty the cache
			fCachePaths.clear();
		} else {
			File file = new File(fDBDir, path);

			debug("Delete \"" + file.getAbsolutePath() + "\"");

			if (file.isDirectory()) {
				delete_tree(new SubProgressMonitor(monitor, 1), file);
			} else if (file.isFile()) {
				file.delete();
				monitor.worked(1);
			}
		}
		monitor.done();
	}
	
	public void mkdirs(String path) {
		File file = new File(fDBDir, path);
		
		if (!file.isDirectory()) {
			file.mkdirs();
		}
	}
	
	private void async_clear(File root) {
		Random r = new Random(System.currentTimeMillis());

		final File newname = new File(root.getParentFile(), 
				root.getName() + "_" + Math.abs(r.nextInt()));
		if (!root.renameTo(newname)) {
			fLog.debug(LEVEL_MIN, "Failed to rename cache directory");
			// delete in-line
			delete_tree(null, root);
			return;
		}
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "Removing cache: rename to " + newname.getAbsolutePath());
		}

		IJobMgr job_mgr = SVCorePlugin.getJobMgr();
		IJob job = job_mgr.createJob();
		// Set low priority
		job.setPriority(10);
		job.init("Remove Cache", new Runnable() {
			public void run() {
				if (fDebugEn) {
					fLog.debug(LEVEL_MID, "Deleteing old cache");
				}
				delete_tree(null, newname);
			}
		});
		job_mgr.queueJob(job);
	}
	
	private void delete_tree(IProgressMonitor monitor, File p) {
		if (monitor == null) {
			monitor = new NullProgressMonitor();
		}
		if (p.isFile()) {
			monitor.beginTask("Delete Cache File", 1);
			p.delete();
			monitor.worked(1);
			monitor.done();
		} else {
			if (p.exists()) {
				File file_l[] = p.listFiles();
				if (file_l != null) {
					monitor.beginTask("Delete Cache", file_l.length);
					for (File f : file_l) {
						if (f.getName().equals("..") || f.getName().equals(".")) {
							debug("[ERROR] " + f.getName());
							continue;
						}
						if (f.isFile()) {
							f.delete();
							monitor.worked(1);
						}
						else if (f.isDirectory()) {
							delete_tree(new SubProgressMonitor(monitor, 1), f);
						}
					}
					monitor.done();
				}
				p.delete();
			}
		}
	}

	public void sync() throws IOException {
		// TODO Auto-generated method stub

	}
	
	private void debug(String msg) {
		// TODO:
	}

	private void loadDBPaths(File parent) {
		File files[] = parent.listFiles();
		if (files != null) {
			for (File f : files) {
				if (f.isDirectory()) {
					loadDBPaths(f);
				} else if (f.isFile()) {
					fCachePaths.add(f.getAbsolutePath());
				}
			}
		}
	}
}

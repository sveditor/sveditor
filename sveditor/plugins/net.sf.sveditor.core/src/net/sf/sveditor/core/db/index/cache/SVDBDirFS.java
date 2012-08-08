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
import java.util.List;
import java.util.Random;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.job_mgr.IJob;
import net.sf.sveditor.core.job_mgr.IJobMgr;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBDirFS implements ISVDBFS, ILogLevelListener {
	private File				fDBDir;
	private boolean			fAsyncClear = true;
	private boolean			fDebugEn;
	private LogHandle			fLog;
	
	public SVDBDirFS(File root) {
		fDBDir = root;
		fLog = LogFactory.getLogHandle("SVDBDirFS");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
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
	
	public void delete(String path) {
		if (path.equals("")) {
			if (fDBDir.exists()) {
				if (fAsyncClear) {
					async_clear(fDBDir);
				} else {
					delete_tree(fDBDir);
				}
			}
		} else {
			File file = new File(fDBDir, path);

			debug("Delete \"" + file.getAbsolutePath() + "\"");

			if (file.isDirectory()) {
				delete_tree(file);
			} else if (file.isFile()) {
				file.delete();
			}
		}
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
			delete_tree(root);
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
				delete_tree(newname);
			}
		});
		job_mgr.queueJob(job);
	}
	
	private void delete_tree(File p) {
		if (p.isFile()) {
			p.delete();
		} else {
			if (p.exists()) {
				File file_l[] = p.listFiles();
				if (file_l != null) {
					for (File f : file_l) {
						if (f.getName().equals("..") || f.getName().equals(".")) {
							debug("[ERROR] " + f.getName());
							continue;
						}
						if (f.isDirectory()) {
							delete_tree(f);
						}
					}
				}
				file_l = p.listFiles();
				if (file_l != null) {
					for (File f : file_l) {
						if (f.getName().equals("..") || f.getName().equals(".")) {
							debug("[ERROR] " + f.getName());
							continue;
						}
						if (f.isFile()) {
							f.delete();
						}
					}
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

}

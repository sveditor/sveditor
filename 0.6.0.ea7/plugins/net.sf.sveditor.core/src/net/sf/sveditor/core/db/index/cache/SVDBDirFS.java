package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.RandomAccessFile;
import java.util.List;

public class SVDBDirFS implements ISVDBFS {
	private File				fDBDir;
	
	public SVDBDirFS(File root) {
		fDBDir = root;
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
				delete_tree(fDBDir);
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
	
	private void delete_tree(File p) {
		if (p.isFile()) {
			p.delete();
		} else {
			if (p.exists()) {
				for (File f : p.listFiles()) {
					if (f.getName().equals("..") || f.getName().equals(".")) {
						debug("[ERROR] " + f.getName());
						continue;
					}
					if (f.isDirectory()) {
						delete_tree(f);
					}
				}
				for (File f : p.listFiles()) {
					if (f.getName().equals("..") || f.getName().equals(".")) {
						debug("[ERROR] " + f.getName());
						continue;
					}
					if (f.isFile()) {
						f.delete();
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

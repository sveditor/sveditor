package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public class SVDBDirFS implements ISVDBFS {
	private File				fDBDir;
	
	public SVDBDirFS(File root) {
		fDBDir = root;
	}

	public InputStream openFileRead(String path) {
		InputStream ret = null;
		try {
			ret = new FileInputStream(new File(fDBDir, path));
		} catch (IOException e) {}
		
		return ret;
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
	
	public void close(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {}
	}

	public boolean fileExists(String path) {
		File file = new File(fDBDir, path);
		return file.exists();
	}
	
	public long lastModified(String path) {
		File file = new File(fDBDir, path);
		
		return file.lastModified();
	}
	
	public void delete(String path) {
		if (path.equals("")) {
			delete_tree(fDBDir);
		} else {
			File file = new File(fDBDir, path);

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
		for (File f : p.listFiles()) {
			if (f.getName().equals("..") || f.getName().equals(".")) {
				System.out.println("[ERROR] " + f.getName());
				continue;
			}
			if (f.isDirectory()) {
				delete_tree(f);
			}
		}
		for (File f : p.listFiles()) {
			if (f.getName().equals("..") || f.getName().equals(".")) {
				System.out.println("[ERROR] " + f.getName());
				continue;
			}
			if (f.isFile()) {
				f.delete();
			}
		}
	}

	public void sync() throws IOException {
		// TODO Auto-generated method stub

	}

}

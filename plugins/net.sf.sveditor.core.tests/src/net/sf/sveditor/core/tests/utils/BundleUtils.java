package net.sf.sveditor.core.tests.utils;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Enumeration;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.osgi.framework.Bundle;

public class BundleUtils {
	private Bundle			fBundle;
	
	public BundleUtils(Bundle bundle) {
		fBundle = bundle;
	}
	
	@SuppressWarnings("unchecked")
	public void copyBundleDirToFS(
			String			bundle_dir,
			File			fs_path) {
		Enumeration	entries = fBundle.findEntries(bundle_dir, "*", true);
		byte tmp[] = new byte[1024*1024];
		
		String dirname = new File(bundle_dir).getName();
		fs_path = new File(fs_path, dirname);

		while (entries.hasMoreElements()) {
			URL url = (URL)entries.nextElement();
			
			if (url.getPath().endsWith("/")) {
				// Directory
				continue;
			}
			
			String file_subpath = url.getPath().substring(bundle_dir.length());
			File target = new File(fs_path, file_subpath);
			
			if (!target.getParentFile().exists()) {
				if (!target.getParentFile().mkdirs()) {
					System.out.println("[ERROR] Failed to create directory \"" + 
							target.getParent() + "\"");
				}
			}
			
			try {
				FileOutputStream out = new FileOutputStream(target);
				InputStream in = url.openStream();
				int len;

				do {
					len = in.read(tmp, 0, tmp.length);
					if (len > 0) {
						out.write(tmp, 0, len);
					}
				} while (len > 0);
				
				out.close();
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	@SuppressWarnings("unchecked")
	public void copyBundleDirToWS(
			String			bundle_dir,
			IContainer		ws_path) {
		Enumeration	entries = fBundle.findEntries(bundle_dir, "*", true);
		
		String dirname = new File(bundle_dir).getName();
		ws_path = ws_path.getFolder(new Path(dirname));

		while (entries.hasMoreElements()) {
			URL url = (URL)entries.nextElement();
			
			if (url.getPath().endsWith("/")) {
				// Directory
				continue;
			}
			
			String file_subpath = url.getPath().substring(bundle_dir.length());
			IFile target = ws_path.getFile(new Path(file_subpath));

			IFolder parent = (IFolder)target.getParent();
			
			
			try {
				if (!parent.exists()) {
					parent.create(true, false, new NullProgressMonitor());
				}
				
				InputStream in = url.openStream();
				
				if (target.exists()) {
					target.setContents(in, true, false, new NullProgressMonitor());
				} else {
					target.create(in, true, new NullProgressMonitor());
				}
				
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	public ByteArrayOutputStream readBundleFile(String bundle_path) {
		URL url = fBundle.getEntry(bundle_path);
		ByteArrayOutputStream ret = new ByteArrayOutputStream();
		
		try {
			InputStream in = url.openStream();
			byte tmp[] = new byte[1024*1024];
			int len;
			
			do {
				if ((len = in.read(tmp, 0, tmp.length)) > 0) {
					ret.write(tmp, 0, len);
				}
				if (len > 0);
			} while (len > 0);
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
		
		return ret;
	}
}

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


package org.eclipse.hdt.sveditor.core;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.URL;
import java.util.Enumeration;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.osgi.framework.Bundle;

public class BundleUtils {
	private Bundle			fBundle;
	
	public BundleUtils(Bundle bundle) {
		fBundle = bundle;
	}
	
	public void copyBundleFileToFS(
			String			bundle_file,
			File			fs_path) throws IOException {
		URL url = fBundle.getEntry(bundle_file);
		byte tmp[] = new byte[1024*1024];
	
		File outfile;
		if (fs_path.isDirectory()) {
			String leafname = new File(bundle_file).getName();
			outfile = new File(fs_path, leafname);
		} else {
			outfile = fs_path;
		}
		
		if (!fs_path.getParentFile().isDirectory()) {
			fs_path.mkdirs();
		}

		FileOutputStream out = new FileOutputStream(outfile);
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
	}

	public void copyBundleFileToFSText(
			String			bundle_file,
			File			fs_path) throws IOException {
		URL url = fBundle.getEntry(bundle_file);
	
		File outfile;
		if (fs_path.isDirectory()) {
			String leafname = new File(bundle_file).getName();
			outfile = new File(fs_path, leafname);
		} else {
			outfile = fs_path;
		}
		
		if (!fs_path.getParentFile().isDirectory()) {
			fs_path.mkdirs();
		}

		FileOutputStream out = new FileOutputStream(outfile);
		InputStream in = url.openStream();
		
		BufferedReader rdr = new BufferedReader(new InputStreamReader(in));
		PrintStream ps = new PrintStream(out);

		String str;
		while ((str = rdr.readLine()) != null) {
			ps.println(str);
		}

		ps.close();
		in.close();
	}
	
	@SuppressWarnings("rawtypes")
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
					throw new RuntimeException("Failed to create directory \"" + target.getParent() + "\"");
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
				throw new RuntimeException("Failed to copy file " + target);
			}
		}
	}
	
	public void unpackBundleZipToFS(
			String			bundle_path,
			File			fs_path) {
		URL zip_url = fBundle.getEntry(bundle_path);
//		TestCase.assertNotNull(zip_url);
		
		if (!fs_path.isDirectory()) {
			fs_path.mkdirs();
		}
		
		try {
			InputStream in = zip_url.openStream();
//			TestCase.assertNotNull(in);
			byte tmp[] = new byte[4*1024];
			int cnt;

			ZipInputStream zin = new ZipInputStream(in);
			ZipEntry ze;

			while ((ze = zin.getNextEntry()) != null) {
				// System.out.println("Entry: \"" + ze.getName() + "\"");
				File entry_f = new File(fs_path, ze.getName());
				if (ze.getName().endsWith("/")) {
					// Directory
					continue;
				}
				if (!entry_f.getParentFile().exists()) {
//					TestCase.assertTrue(entry_f.getParentFile().mkdirs());
					entry_f.getParentFile().mkdirs();
				}
				FileOutputStream fos = new FileOutputStream(entry_f);
				BufferedOutputStream bos = new BufferedOutputStream(fos, tmp.length);
				
				while ((cnt = zin.read(tmp, 0, tmp.length)) > 0) {
					bos.write(tmp, 0, cnt);
				}
				bos.flush();
				bos.close();
				fos.close();
			
				zin.closeEntry();
			}
			zin.close();
		} catch (IOException e) {
			e.printStackTrace();
//			TestCase.fail("Failed to unpack zip file: " + e.getMessage());
		}
	}

	public void copyBundleFileToWS(
			String			bundle_path,
			IContainer		ws_path) {
		URL url = fBundle.getEntry(bundle_path);
		
		String bundle_filename = new File(bundle_path).getName();
		IFile target = ws_path.getFile(new Path(bundle_filename));

		IContainer parent = target.getParent();
			
			
		try {
			if (!parent.exists()) {
				createDirTree(parent);
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


	@SuppressWarnings("rawtypes")
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
					createDirTree(parent);
//					parent.create(true, false, new NullProgressMonitor());
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
	
	private void createDirTree(IContainer dir) throws CoreException {
		if (dir.getParent() != null) {
			if (!dir.getParent().exists()) {
				createDirTree(dir.getParent());
			}
		}
		((IFolder)dir).create(true, false, new NullProgressMonitor());
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
	
	public boolean deleteWSFile(IContainer parent, String path) {
		IFile file = parent.getFile(new Path(path));
		
		try {
			file.delete(true, new NullProgressMonitor());
		} catch (CoreException e) {
			return false;
		}
		return true;
	}
}

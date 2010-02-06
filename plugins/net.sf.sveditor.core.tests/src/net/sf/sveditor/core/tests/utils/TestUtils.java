/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.utils;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestUtils {
	
	private static byte[]			fTmp;
	
	static {
		fTmp = new byte[1024*1024];
	}
	
	public static File createTempDir() {
		File tmpdir = new File(System.getProperty("java.io.tmpdir"));
		File ret = null;

		for (int i=0; i<10000; i++) {
			File try_dir = new File(tmpdir, "sveditor_tmp_" + i);

			if (!try_dir.exists()) {
				ret = try_dir;
				if (!ret.mkdirs()) {
					System.out.println("[ERROR] cannot create tmpdir");
				}
				break;
			}
		}
		
		return ret;
	}
	
	public static void copy(ByteArrayOutputStream in, File out) {
		try {
			OutputStream out_s = new FileOutputStream(out);
			InputStream  in_s = new ByteArrayInputStream(in.toByteArray());
	
			int len;
			
			do {
				len = in_s.read(fTmp, 0, fTmp.length);
				if (len > 0) {
					out_s.write(fTmp, 0, len);
				}
			} while (len > 0);
			
			out_s.close();
		} catch (IOException e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}

	public static void copy(ByteArrayOutputStream in, IFile out) {
		try {
			InputStream  in_s = new ByteArrayInputStream(in.toByteArray());

			if (out.exists()) {
				out.setContents(in_s, true, false, new NullProgressMonitor());
			} else {
				out.create(in_s, true, new NullProgressMonitor());
			}
		} catch (Exception e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}

	public static IProject createProject(String name) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		IProject project = root.getProject(name);
		
		try {
			if (project.exists()) {
				project.delete(true, true, new NullProgressMonitor());
			}

			project.create(new NullProgressMonitor());
			
			if (!project.isOpen()) {
				project.open(new NullProgressMonitor());
			}
		} catch (CoreException e) {
			e.printStackTrace();
			throw new RuntimeException("Failed to create project");
		}
		
		return project;
	}
	

}

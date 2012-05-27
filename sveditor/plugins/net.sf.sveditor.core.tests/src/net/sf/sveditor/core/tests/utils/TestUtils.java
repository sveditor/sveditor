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
import java.net.URI;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import junit.framework.TestFailure;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.osgi.framework.Bundle;

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
	
	public static String readInput(InputStream in) {
		StringBuilder sb = new StringBuilder();
		byte tmp[] = new byte[1024];
		int len;
		
		try {
			while ((len = in.read(tmp, 0, tmp.length)) > 0) {
				sb.append(new String(tmp, 0, len));
			}
		} catch (IOException e) {
			
		}
		return sb.toString();
	}
	
	public static void delete(File item) {
		if (item.isDirectory()) {
			for (File i : item.listFiles()) {
				delete(i);
			}
		}
		if (!item.delete()) {
			TestCase.fail("Failed to delete \"" + item.getAbsolutePath() + "\"");
		}
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
		return createProject(name, null);
	}
	
	public static IProject setupIndexWSProject(
			Bundle				bundle,
			File				tmpdir,
			String 				name,
			String				data_file) {
		if (bundle == null) {
			bundle = SVCoreTestsPlugin.getDefault().getBundle();
		}
		BundleUtils utils = new BundleUtils(bundle);
		IProject project = TestUtils.createProject(name, 
				new File(tmpdir, name));
		
		if (data_file.endsWith(".zip")) {
			TestCase.fail(".zip file unsupported");
			utils.copyBundleDirToWS(data_file, project);
		} else {
			utils.copyBundleDirToWS(data_file, project);
		}
		
		File db = new File(tmpdir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}
		TestCase.assertTrue(db.mkdirs());
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
	
		return project;
	}

	public static IProject createProject(String name, File path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		URI location = null;
		
		if (path != null) {
			location = path.toURI();
		}
		
		IProject project = root.getProject(name);
		
		try {
			if (project.exists()) {
				project.close(new NullProgressMonitor());
			}
		} catch (CoreException e) {
			e.printStackTrace();
//			throw new RuntimeException("Failed to close existing project: " + e.getMessage());
		}
		try {
			if (project.exists()) {
				project.delete(true, true, new NullProgressMonitor());
			}
		} catch (CoreException e) {
			e.printStackTrace();
			throw new RuntimeException("Failed to close existing project: " + e.getMessage());
		}

		try {
			IProjectDescription desc = project.getWorkspace().newProjectDescription(name);
			desc.setLocationURI(location);
			
			project.create(desc, new NullProgressMonitor());
			
			if (!project.isOpen()) {
				project.open(new NullProgressMonitor());
			}
		} catch (CoreException e) {
			e.printStackTrace();
			throw new RuntimeException("Failed to create project: " + e.getMessage());
		}
		
		return project;
	}

	public static void deleteProject(IProject project_dir) {
		try {
			project_dir.close(new NullProgressMonitor());
			project_dir.delete(true, true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public static void assertContains(List<String> list, String ... expected) {
		List<String> temp = new ArrayList<String>();
		temp.addAll(list);
		
		for (String exp : expected) {
			if (temp.contains(exp)) {
				temp.remove(exp);
			} else {
				TestCase.fail("List does not contain \"" + exp + "\"");
			}
		}
		
		if (temp.size() > 0) {
			StringBuilder leftovers = new StringBuilder();
			
			for (String l : temp) {
				leftovers.append(l);
				leftovers.append(" ");
			}
			TestCase.fail("List contains unexpected elements {" + leftovers + "}");
		}
	}
	
	public static <T> HashSet<T> newHashSet(T... objs) {
	    HashSet<T> set = new HashSet<T>();
	    for (T o : objs) {
	        set.add(o);
	    }
	    return set;
	}
	
}

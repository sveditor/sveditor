/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.utils;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URI;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVProjectBuilder;
import net.sf.sveditor.core.SVProjectNature;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;

import org.eclipse.core.internal.events.BuildCommand;
import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.osgi.framework.Bundle;

public class TestUtils {
	
	private static byte[]			fTmp;
	
	static {
		fTmp = new byte[1024*1024];
	}
	
	public static InputStream openFile(File file) {
		try {
			InputStream in = new FileInputStream(file);
			
			return in;
		} catch (IOException e) {
			TestCase.fail("Failed to open " + file.getAbsolutePath() + " for reading");
		}
		
		return null;
	}
	
	public static void closeStream(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {
			TestCase.fail("Failed to close input stream");
		}
	}
	
	public static File createTempDir() {
		File tmpdir = new File(System.getProperty("java.io.tmpdir"));
		File ret = null;
	
		UUID uuid = UUID.randomUUID();
		ret = new File(tmpdir, 
				"sveditor_tmp_" + uuid.toString());
		
		TestCase.assertFalse(ret.exists());
		TestCase.assertTrue(ret.mkdirs());
	
		return ret;

		/*

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
		 */
	}
	
	public static void unpackZipToFS(
			File			zipfile_path,
			File			fs_path) {
		if (!fs_path.isDirectory()) {
			TestCase.assertTrue(fs_path.mkdirs());
		}
		
		try {
			InputStream in = new FileInputStream(zipfile_path);
			TestCase.assertNotNull(in);
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
					TestCase.assertTrue(entry_f.getParentFile().mkdirs());
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
			TestCase.fail("Failed to unpack zip file: " + e.getMessage());
		}			
	}
	
	public static String read(IFile file) {
		String ret = null;
		try {
			InputStream in = file.getContents();
			ret = readInput(in);
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		return ret;
	}
			
	public static String readInput(InputStream in) {
		return readInputSB(in).toString();
	}
	
	public static StringBuilder readInputSB(InputStream in) {
		StringBuilder sb = new StringBuilder();
		byte tmp[] = new byte[1024];
		int len;
		
		try {
			while ((len = in.read(tmp, 0, tmp.length)) > 0) {
				sb.append(new String(tmp, 0, len));
			}
		} catch (IOException e) {
			
		}
		return sb;
	}
	
	public static void delete(File item) {
		if (item.isDirectory()) {
			for (File i : item.listFiles()) {
				delete(i);
			}
		}
		
		for (int i=0; i<2; i++) {
			if (item.exists()) {
				if (!item.delete()) {
					if( i == 0) {
						try {
							Thread.sleep(200);
						} catch (InterruptedException e) {}
					} else {
						if (item.isDirectory()) {
							StringBuilder ex_files = new StringBuilder();
							File files[] = item.listFiles();
							if (files != null) {
								for (File f : files) {
									ex_files.append(f.getName() + " ");
								}
							}
							TestCase.fail("Failed to delete directory \"" + item.getAbsolutePath() + "\" sub-files: " + ex_files.toString());
						} else {
							TestCase.fail("Failed to delete file \"" + item.getAbsolutePath() + "\"");
						}
					}
				}
			}
		}
	}

	public static boolean safe_delete(File item) {
		if (item.isDirectory()) {
			File files[] = item.listFiles();
			
			if (files != null) {
				for (File i : files) {
					if (!safe_delete(i)) {
						return false;
					}
				}
			}
		}
		
		if (item.exists()) {
			if (!item.delete()) {
				return false;
			} 
		}
		
		return true;
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
	
	public static void copy_ws(String in, String ws_path) {
		TestCase.assertTrue(ws_path.startsWith("${workspace_loc}"));
		
		ws_path = ws_path.substring("${workspace_loc}".length());
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IFile file = root.getFile(new Path(ws_path));
		
		copy(in, file);
	}
	
	public static void copy(String in, IFile out) {
		try {
			InputStream  in_s = new StringInputStream(in);

			if (out.exists()) {
				out.setContents(in_s, true, false, new NullProgressMonitor());
			} else {
				out.create(in_s, true, new NullProgressMonitor());
			}
		} catch (Exception e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}

	public static void copy(String in, File out) {
		try {
			PrintStream ps = new PrintStream(out);
			ps.print(in);
			ps.close();
		} catch (Exception e) {
			throw new RuntimeException("Failed to write file \"" + out + "\"");
		}
	}
	
	public static IFolder mkdir(IContainer c, String dir) {
		IFolder f = c.getFolder(new Path(dir));
		
		try {
			f.create(true, true, new NullProgressMonitor());
		} catch (CoreException e) {
			TestCase.fail("Failed to create directory \"" + dir + "\": " + e.getMessage());
		}
		
		return f;
	}
	
	public static IProject createProject(String name) {
		return createProject(name, null);
	}
	
	public static Tuple<IProject, SVDBProjectData> createSVEProject(
			String				name,
			File				location) {
		IProject p = createProject(name, location);
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(p);
		
		SVProjectNature.ensureHasSvProjectNature(p);
	
		return new Tuple<IProject, SVDBProjectData>(p, pdata);
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
		
		SVProjectNature.ensureHasSvProjectNature(project);
		
		return project;
	}

	public static void deleteProject(final String testname, final IProject project_dir) {
		if (project_dir != null && project_dir.exists()) {
			Job delete_job = new Job("Delete Project " + project_dir.getName()) {
				
				@Override
				protected IStatus run(IProgressMonitor monitor) {
					try {
						project_dir.close(new NullProgressMonitor());
						project_dir.delete(true, true, new NullProgressMonitor());
					} catch (CoreException e) {
						System.out.println("Test: " + testname + " Failed to delete project: " + project_dir.getName());
						e.printStackTrace();
						TestCase.fail("Failed to delete project " + project_dir.getFullPath() + ": " +
								e.getMessage());
					}

					return Status.OK_STATUS;
				}
			};
		
			delete_job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			delete_job.schedule();
			try {
				delete_job.join();
			} catch (InterruptedException e) {
				
			}
		}
	}
	
	private static void delete(IContainer parent) throws CoreException {
		for (IResource r : parent.members()) {
			if (r instanceof IContainer) {
				delete((IContainer)r);
			}
		}
		for (IResource r : parent.members()) {
			if (!(r instanceof IContainer)) {
				r.delete(true, new NullProgressMonitor());
			}
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
	
	public static List<String> fileToLines(String filename) throws IOException {
		List<String> lines = new LinkedList<String>();
		String line = "";
		BufferedReader in = new BufferedReader(new FileReader(filename)) ;
		while ((line = in.readLine()) != null) {
			lines.add(line);
		}
		in.close();
		return lines;
	}	
	
	public static IProject importProject(final File project) {
		final IWorkspace ws = ResourcesPlugin.getWorkspace();
		final IWorkspaceRoot root = ws.getRoot();
		final List<IProject> result = new ArrayList<IProject>();
		
		Job import_job = new Job("Import " + project.getName()) {
			
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				IProjectDescription pd = null;
				
				try {
					pd = ws.loadProjectDescription(
							new Path(new File(project, ".project").getAbsolutePath()));
				} catch (CoreException e) {
					TestCase.fail("Failed to load project description: " + 
							project.getAbsolutePath() + ": " + e.getMessage());
				}
			
				IProject p = root.getProject(pd.getName());
				
				try {
					p.create(pd, null);
					p.open(null);
				} catch (CoreException e) {
					TestCase.fail("Failed to open project: " + 
							project.getAbsolutePath() + ": " + e.getMessage());
				}
				
				result.add(p);
				
				return Status.OK_STATUS;
			}
		};
		
		import_job.setRule(root);
		import_job.schedule();
		try {
			import_job.join();
		} catch (InterruptedException e) {}
		
		return result.get(0);
	}

	public static List<String> grep(
			List<String>			in,
			String					or_list[],
			String					and_list[]) {
		List<String> ret = new ArrayList<String>();
		Pattern or_pattern_list[] = new Pattern[or_list.length];
		Pattern and_pattern_list[] = new Pattern[and_list.length];
		
		for (int i=0; i<or_list.length; i++) {
			or_pattern_list[i] = Pattern.compile(or_list[i]);
		}
		
		for (int i=0; i<and_list.length; i++) {
			and_pattern_list[i] = Pattern.compile(and_list[i]);
		}
	
			for (String line : in) {
				boolean have_match = false;
				
				for (Pattern p : or_pattern_list) {
					if (p.matcher(line).matches()) {
						have_match = true;
						break;
					}
				}
			
				if (have_match) {
					for (Pattern p : and_pattern_list) {
						if (!p.matcher(line).matches()) {
							have_match = false;
						}
					}
				}
				
				if (have_match) {
					ret.add(line);
				}
			}
	
		return ret;
	}
	
	public static List<String> read(InputStream in) {
		String line;
		InputStreamReader rdr = new InputStreamReader(in);
		BufferedReader reader = new BufferedReader(rdr);
		List<String> ret = new ArrayList<String>();
		
		try {
			while ((line = reader.readLine()) != null) {
				ret.add(line);
			}
		} catch (IOException e) {}
		
		return ret;
	}
	
	public static List<String> sed(
			List<String> in,
			String patterns[]) {
		List<String> ret = new ArrayList<String>();
		Pattern pattern_list[] = new Pattern[patterns.length];
		String replace_list[] = new String[patterns.length];
		
		for (int i=0; i<patterns.length; i++) {
			char first_ch = patterns[i].charAt(0);
			int end_pattern_idx = patterns[i].indexOf(first_ch, 1);
			String pattern = patterns[i].substring(1, end_pattern_idx);
			int end_replace_idx = patterns[i].indexOf(first_ch, end_pattern_idx+1);
			String replace = patterns[i].substring(end_pattern_idx+1, end_replace_idx);
			
			pattern_list[i] = Pattern.compile(pattern);
			replace_list[i] = replace;
		}
		
		for (String line : in) {
			for (int i=0; i<patterns.length; i++) {
				line = pattern_list[i].matcher(line).replaceAll(replace_list[i]);
			}
		
			ret.add(line);
		}
		
		return ret;
	}
	
	public static void setProjectFileWrapper(SVDBProjectData pdata, SVProjectFileWrapper fw) {
		pdata.setProjectFileWrapper(fw, true);
		
		// Sleep to ensure settings are propagated
		try {
			Thread.sleep(100);
		} catch (InterruptedException e) {}
	}
}

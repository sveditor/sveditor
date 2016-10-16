package net.sf.sveditor.svutils.tests;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogListener;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class SVUtilsTestBase extends TestCase implements ILogListener {
	List<String>				fInfoMessages = new ArrayList<String>();
	File						fTestProjectDir = null;
	File						fTmpDir;
	
	
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		TestUtils.delete(fTmpDir);
	}

	public void copyResourceDir(String path, File dest) {
		if (fTestProjectDir == null) {
			String cp[] = System.getProperty("java.class.path").split(File.pathSeparator);
			
			for (String cp_e : cp) {
				File cp_f = new File(cp_e);
			
				if (cp_f.getParentFile() != null && 
						cp_f.getParentFile().getName().equals("svutils_tests")) {
					fTestProjectDir = cp_f.getParentFile();
					break;
				}
			}
			
			File path_f = new File(fTestProjectDir, path);
			
			TestCase.assertTrue(path_f.isDirectory());
			
			copy(path_f, dest);
	
//			String tpd_s = fTestProjectDir.getAbsolutePath();
//			String dest_s = dest.getAbsolutePath();
//			for (File f : path_f.listFiles()) {
//				String f_s = f.getAbsolutePath();
//				
//				String rp_s = f_s.substring(tpd_s.length()); // path relative to the source location
//				File d = new File(dest, rp_s);
//						
//				if (f.isDirectory()) {
//					// Create the directory
//					d.mkdirs();
//					System.out.println("Mkdir(D) " + f);
//				} else {
//					// Create the parent directory if it doesn't exist
//					if (!d.getParentFile().isDirectory()) {
//						d.getParentFile().mkdirs();
//						System.out.println("Mkdir " + d);
//					}
//					// Now, copy the file
//					System.out.println("Copy " + rp_s);
//				}
//			}
//			
//			System.out.println("TestProjectDir: " + fTestProjectDir);
			
		}
	}
	
	private static void copy(File src, File dst) {
		byte tmp[] = new byte[4096];
		int sz;
		
		for (File f : src.listFiles()) {
			if (f.isDirectory()) {
				File d = new File(dst, f.getName());
				// Create the directory
				d.mkdirs();
				copy(f, d);
			} else {
				try {
					InputStream in = new FileInputStream(f);
					OutputStream out = new FileOutputStream(new File(dst, f.getName()));
					while ((sz = in.read(tmp, 0, tmp.length)) > 0) {
						out.write(tmp, 0, sz);
					}
					in.close();
					out.close();
				} catch (IOException e) {
					e.printStackTrace();
					TestCase.fail("Failed to copy file " + f);
				}
			}
		}		
	}

	@Override
	public void message(ILogHandle handle, int type, int level, String message) {
		switch (type) {
		case Type_Info: fInfoMessages.add(message); break;
		}
	}
	

}

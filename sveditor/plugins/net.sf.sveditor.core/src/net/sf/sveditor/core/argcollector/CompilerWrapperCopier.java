package net.sf.sveditor.core.argcollector;

import java.io.File;
import java.io.IOException;

import net.sf.sveditor.core.BundleUtils;
import net.sf.sveditor.core.SVCorePlugin;

public class CompilerWrapperCopier {
	
	public static File copy(File dest, boolean target_os_only) throws IOException {
		BundleUtils utils = new BundleUtils(SVCorePlugin.getDefault().getBundle());
		String os = System.getProperty("os.name");
		String wrappers[] = {
				"iverilog",
				"vcs",
				"vlog",
				"qverilog",
				"ncvlog",
				"irun"
		};
		
		if (os.toLowerCase().contains("win")) {
			os = "windows";
		} else {
			os = "unix";
		}
		
		String os_l[];
		
		if (target_os_only) {
			os_l = new String[] {os};
		} else {
			os_l = new String[] {"unix", "windows"};
		}

		for (String t_os : os_l) {
			File os_dir = new File(dest, t_os);
			
			os_dir.mkdirs();
			
			for (String wrapper : wrappers) {
				String wrapper_src = "/sve_compiler_wrappers/" + t_os;
				wrapper_src += "/wrapper";
				
				if (t_os.equals("windows")) {
					wrapper_src += ".exe";
					wrapper += ".exe";
				}
				
				File wrapper_f = new File(os_dir, wrapper);
				
				utils.copyBundleFileToFS(wrapper_src, wrapper_f);
			
				wrapper_f.setExecutable(true);
			}

			// Create the root wrapper
			String wrapper = "sve_collect_compiler_args";
			String wrapper_src = "/sve_compiler_wrappers/" + t_os;
			
			if (t_os.equals("windows")) {
				wrapper += ".exe";
			}
			
			wrapper_src += "/" + wrapper;
			
			File wrapper_f = new File(os_dir, wrapper);
			
			utils.copyBundleFileToFS(wrapper_src, wrapper_f);
		
			wrapper_f.setExecutable(true);			
		}
		
		return new File(dest, os);
	}

}

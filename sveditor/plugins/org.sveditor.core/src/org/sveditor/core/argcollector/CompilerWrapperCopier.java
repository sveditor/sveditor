/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.argcollector;

import java.io.File;
import java.io.IOException;

import org.sveditor.core.BundleUtils;
import org.sveditor.core.SVCorePlugin;

public class CompilerWrapperCopier {
	
	public static File copy(File dest, boolean target_os_only) throws IOException {
		boolean is_win;
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
			is_win = true;
		} else {
			os = "unix";
			is_win = false;
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
				
				if (is_win) {
					wrapper_src += ".exe";
					wrapper += ".exe";
				}
				
				File wrapper_f = new File(os_dir, wrapper);

				if (is_win) {
					utils.copyBundleFileToFS(wrapper_src, wrapper_f);
				} else {
					utils.copyBundleFileToFSText(wrapper_src, wrapper_f);
				}
			
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
		
			if (is_win) {
				utils.copyBundleFileToFS(wrapper_src, wrapper_f);
			} else {
				utils.copyBundleFileToFSText(wrapper_src, wrapper_f);
			}
		
			if (!wrapper_f.setExecutable(true)) {
				System.out.println("Failed to make " + wrapper_f.getAbsolutePath() + " executable");
			}
		}
	
		return new File(dest, os);
	}

}

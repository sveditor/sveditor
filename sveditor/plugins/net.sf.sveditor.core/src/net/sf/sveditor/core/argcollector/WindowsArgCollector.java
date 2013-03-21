package net.sf.sveditor.core.argcollector;

import java.io.File;

import net.sf.sveditor.core.BundleUtils;
import net.sf.sveditor.core.SVCorePlugin;

public class WindowsArgCollector extends AbstractArgCollector {

	@Override
	protected File copyWrapperFiles(File dest) {
		BundleUtils utils = new BundleUtils(SVCorePlugin.getDefault().getBundle());
		
		utils.copyBundleDirToFS(
				"/sve_compiler_wrappers/windows",
				dest);
		
		File windows = new File(dest, "windows");
		/*
		File files[] = windows.listFiles();
		for (File f : files) {
			f.setExecutable(true);
		}
		 */
		
		return new File(windows, "sve_collect_compiler_args.bat");		
	}

}

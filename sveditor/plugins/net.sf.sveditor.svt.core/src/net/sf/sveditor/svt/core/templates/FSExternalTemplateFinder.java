package net.sf.sveditor.core.templates;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.LogFactory;

public class FSExternalTemplateFinder extends AbstractExternalTemplateFinder {
	private File				fPath;
	
	public FSExternalTemplateFinder(File path) {
		super(new FSInStreamProvider());
		
		fPath = path;
		fLog = LogFactory.getLogHandle("FSExternalTemplateFinder");
	}

	@Override
	protected List<String> findTemplatePaths() {
		List<String> template_paths = new ArrayList<String>();
		
		findTemplatePaths(template_paths, fPath);
		
		return template_paths;
	}
	
	private void findTemplatePaths(List<String> paths, File path) {
		File files[] = path.listFiles();
		
		if (files != null) {
			for (File file : files) {
				if (file.isDirectory()) {
					findTemplatePaths(paths, file);
				} else if (file.getName().endsWith(".svt")) {
					paths.add(file.getAbsolutePath());
				}
			}
		}
	}

	@Override
	protected List<String> listFiles(String path) {
		File file = new File(path);
		List<String> ret = new ArrayList<String>();
		
		if (file.isDirectory()) {
			File files[] = file.listFiles();
			
			if (files != null) {
				for (File f : files) {
					if (f.isFile()) {
						ret.add(f.getAbsolutePath());
					}
				}
			}
		}
		
		return ret;
	}

	@Override
	protected InputStream openFile(String path) {
		InputStream in = null;
		
		try {
			in = new FileInputStream(path);
		} catch (IOException e) {}
		
		return in;
	}

	@Override
	protected void closeStream(InputStream in) {
		try {
			if (in != null) {
				in.close();
			}
		} catch (IOException e) {}
	}
}

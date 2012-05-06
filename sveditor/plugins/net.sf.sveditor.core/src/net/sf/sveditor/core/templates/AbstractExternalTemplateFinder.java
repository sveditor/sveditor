package net.sf.sveditor.core.templates;

import java.io.File;
import java.io.InputStream;
import java.util.List;

public abstract class AbstractExternalTemplateFinder extends AbstractTemplateFinder {
	private ITemplateInStreamProvider 		fInProvider;
	
	public AbstractExternalTemplateFinder(ITemplateInStreamProvider in_provider) {
		super();
		fInProvider = in_provider;
	}
	
	@Override
	public void find() {
		List<String> paths = findTemplatePaths();
		
		for (String path : paths) {
			InputStream in = openFile(path);
			File tmpl_dir = new File(path).getParentFile();
			
			if (in == null) {
				fLog.error("Failed to open path \"" + path + "\"");
				continue;
			}
			
			// TODO: process template file
			SVTParser p = new SVTParser(tmpl_dir.getPath(), fInProvider);
			
			try {
				p.parse(in);
			} catch (Exception e) {
				fLog.error("Failed to parse template \"" + path + "\": " + e.getMessage(), e);
			}
			
			fCategories.addAll(p.getCategories());
			
			for (TemplateInfo ti : p.getTemplates()) {
				fTemplates.add(ti);
				
				if (!ti.getTemplates().iterator().hasNext()) {
					// implicitly-specified template list
					
					List<String> files = listFiles(tmpl_dir.getPath());
					
					for (String file : files) {
						File f = new File(file);
						if (!f.getName().endsWith(".svt") && 
								!f.getName().startsWith(".")) {
							File fn = new File(file);
							ti.addTemplate(file, fn.getName());
						}
					}
				}
			}
			
			closeStream(in);
		}
	}

	protected abstract List<String> findTemplatePaths();
	
	protected abstract List<String> listFiles(String path);

	protected abstract InputStream openFile(String path);

	protected abstract void closeStream(InputStream in);

}

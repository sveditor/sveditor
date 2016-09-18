package net.sf.sveditor.svt.core.templates;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.log.LogFactory;

public class FilesystemTemplateRegistry extends TemplateRegistry {

	static {
		fLog = LogFactory.getLogHandle("FilesystemTemplateRegistry");
	}
	
	public FilesystemTemplateRegistry() {
		super();
	}

	protected void add_finders(List<AbstractTemplateFinder> finders) {
		// Do nothing
		if (fPathProviders.size() > 0) {
			for (IExternalTemplatePathProvider p : fPathProviders) {
				for (String path : p.getExternalTemplatePath()) {
					fLog.debug(LEVEL_MID, "Processing path \"" + path + "\"");
					finders.add(new FSExternalTemplateFinder(new File(path)));
				}
			}
		}		
	}
}

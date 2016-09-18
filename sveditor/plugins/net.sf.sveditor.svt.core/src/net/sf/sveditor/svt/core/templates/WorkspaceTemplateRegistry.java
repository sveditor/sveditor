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


package net.sf.sveditor.svt.core.templates;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IContainer;

public class WorkspaceTemplateRegistry extends TemplateRegistry implements ILogLevel {
	
	static {
		fLog = LogFactory.getLogHandle("WorkspaceTemplateRegistry");
	}
	
	public WorkspaceTemplateRegistry() {
		super();
	}
	
	protected void add_finders(List<AbstractTemplateFinder> finders) {
		// Do nothing
		if (fPathProviders.size() > 0) {
			for (IExternalTemplatePathProvider p : fPathProviders) {
				for (String path : p.getExternalTemplatePath()) {
					fLog.debug(LEVEL_MID, "Processing path \"" + path + "\"");
					if (path.startsWith("${workspace_loc}")) {
						path = path.substring("${workspace_loc}".length());
						IContainer c = SVFileUtils.getWorkspaceFolder(path);
						finders.add(new WSExternalTemplateFinder(c));
					} else {
						finders.add(new FSExternalTemplateFinder(new File(path)));
					}
				}
			}
		}		
	}

}

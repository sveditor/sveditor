/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class UpdateProjectSettingsJob extends Job 
		implements ILogLevel {
	private SVEditor 						fEditor;
	private String							fProjectName;
	private LogHandle						fLog;
	
	public UpdateProjectSettingsJob(SVEditor editor, String project_name) {
		super(editor.getTitle() + " - Updating project settings");
		fEditor = editor;
		fProjectName = project_name;
		fLog = LogFactory.getLogHandle("UpdateProjectSettingsJob");
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		try {
			fLog.debug(LEVEL_MIN, "Updating index information for file \"" + 
					fEditor.getFilePath() + "\"");

			Tuple<ISVDBIndex, SVDBIndexCollection> result;
			String file_path = fEditor.getFilePath();

			result = SVDBIndexUtil.findIndexFile(file_path, fProjectName, true);

			if (result == null) {
				// Editor should react by creating a shadow index
				fEditor.int_projectSettingsUpdated(null, null);
			} else {
				fEditor.int_projectSettingsUpdated(result.first(), result.second());
			}
		} catch (RuntimeException e) {
			fLog.error("Exception during UpdateProjectSettings", e);
			throw e;
		}
		
		return Status.OK_STATUS;
	}

}

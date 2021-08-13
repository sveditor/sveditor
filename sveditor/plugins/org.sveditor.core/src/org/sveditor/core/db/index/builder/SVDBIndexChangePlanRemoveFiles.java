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
package org.sveditor.core.db.index.builder;

import java.util.ArrayList;
import java.util.List;

public class SVDBIndexChangePlanRemoveFiles extends SVDBIndexChangePlan {
	private List<String>				fFiles;
	
	public SVDBIndexChangePlanRemoveFiles(ISVDBIndexChangePlanner planner) {
		super(planner, SVDBIndexChangePlanType.RemoveFiles);
		fFiles = new ArrayList<String>();
	}
	
	public void addFile(String path) {
		fFiles.add(path);
	}
	
	public List<String> getFiles() {
		return fFiles;
	}

}

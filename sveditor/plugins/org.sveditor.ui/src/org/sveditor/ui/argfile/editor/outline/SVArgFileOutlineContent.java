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
package org.sveditor.ui.argfile.editor.outline;

import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.index.SVDBFilePath;

public class SVArgFileOutlineContent {
	private SVDBFile				fFile;
	private SVDBFilePath			fFilePath;
	
	public SVArgFileOutlineContent(SVDBFile file, SVDBFilePath path) {
		fFile = file;
		fFilePath = path;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}
	
	public SVDBFilePath getFilePath() {
		return fFilePath;
	}
	
}

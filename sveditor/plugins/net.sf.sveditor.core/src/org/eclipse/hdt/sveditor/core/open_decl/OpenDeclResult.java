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
package org.eclipse.hdt.sveditor.core.open_decl;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;

public class OpenDeclResult {

	private SVDBFile				fFile;
	private SVDBFile				fFilePP;
	private ISVDBItemBase			fItem;
	
	public OpenDeclResult(SVDBFile file, SVDBFile pp_file, ISVDBItemBase item) {
		fFile = file;
		fFilePP = pp_file;
		fItem = item;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}
	
	public SVDBFile getFilePP() {
		return fFilePP;
	}
	
	public ISVDBItemBase getItem() {
		return fItem;
	}
	

}

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
package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBFileTreeMacroList extends SVDBItemBase {
	public List<SVDBMacroDef>			fMacroList;
	
	public SVDBFileTreeMacroList() {
		super(SVDBItemType.FileTreeMacroList);
		fMacroList = new ArrayList<SVDBMacroDef>();
	}
	
	public List<SVDBMacroDef> getMacroList() {
		return fMacroList;
	}
	
	public void addMacro(SVDBMacroDef m) {
		for (int i=0; i<fMacroList.size(); i++) {
			if (fMacroList.get(i).getName().equals(m.getName())) {
				fMacroList.remove(i);
				break;
			}
		}
		fMacroList.add(m);
	}

}

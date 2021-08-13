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
package org.eclipse.hdt.sveditor.core.db.index.ops;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBMacroDef;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexOperation;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexOperationRunner;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.search.ISVDBFindNameMatcher;

public class SVDBFindMacroOp implements ISVDBIndexOperation {
	private String						fMacro;
	private SVDBMacroDef				fMacroDef;
	
	public SVDBFindMacroOp(String macro) {
		fMacro = macro;
	}
	
	public SVDBMacroDef getMacroDef() {
		return fMacroDef;
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		if (fMacroDef == null) {
			List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(new NullProgressMonitor(), fMacro, 
					new ISVDBFindNameMatcher() {
						
						public boolean match(ISVDBNamedItem it, String name) {
							return (it.getType() == SVDBItemType.MacroDef &&
									it.getName().equals(name));
						}
					});
			if (result.size() > 0) {
				fMacroDef = (SVDBMacroDef)result.get(0).getSVDBItem();
			}
		}
	}
	
	public static SVDBMacroDef op(
			ISVDBIndexOperationRunner 	runner, 
			String						macro,
			boolean 					sync) {
		SVDBFindMacroOp op = new SVDBFindMacroOp(macro);

		runner.execOp(new NullProgressMonitor(), op, sync);
		
		return op.getMacroDef();
	}

}

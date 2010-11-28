/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBFileMerger {
	
	/**
	 * Merges changes in file_new back to file_ex and collects info
	 * 
	 * @param file_ex
	 * @param file_new
	 * @param adds
	 * @param removes
	 * @param changes
	 */
	public static void merge(
			SVDBFile			file_ex,
			SVDBFile			file_new,
			List<SVDBItem>		adds,
			List<SVDBItem>		removes,
			List<SVDBItem>		changes) {
		merge_scope(file_ex, file_new, adds, removes, changes);
	}
	
	private static int merge_scope(
			ISVDBScopeItem		scope_ex,
			ISVDBScopeItem		scope_new,
			List<SVDBItem>		adds,
			List<SVDBItem>		removes,
			List<SVDBItem>		changes) {
		List<SVDBItem> temp = new ArrayList<SVDBItem>();
		int ret = 0;

		temp.clear();
		// Look for things that were added to scope_new
		for (SVDBItem it_2 : scope_new.getItems()) {
			if (!scope_ex.getItems().contains(it_2)) {
				if (adds != null) {
					adds.add(it_2);
				}
				temp.add(it_2);
			} else {
				SVDBItem it_1 = scope_ex.getItems().get(
						scope_ex.getItems().indexOf(it_2));
				it_1.setLocation(it_2.getLocation());
				if (it_1 instanceof ISVDBScopeItem) {
					((ISVDBScopeItem)it_1).setEndLocation(
							((ISVDBScopeItem)it_2).getEndLocation());
				}
				
				if (it_1 instanceof SVDBTaskFuncScope) {
					SVDBTaskFuncScope tf_1 = (SVDBTaskFuncScope)it_1;
					SVDBTaskFuncScope tf_2 = (SVDBTaskFuncScope)it_2;
					tf_1.getParams().clear();
					tf_1.getParams().addAll(tf_2.getParams());
					tf_1.setReturnType(tf_2.getReturnType());
				}
				temp.add(it_1);
			}
		}
		
		if (removes != null) {
			for (SVDBItem it_1 : scope_ex.getItems()) {
				if (!scope_new.getItems().contains(it_1)) {
					removes.add(it_1);
				}
			}
		}
		
		scope_ex.getItems().clear();
		for (SVDBItem it : temp) {
			if (it instanceof ISVDBScopeItem && scope_new.getItems().contains(it)) {
				merge_scope((ISVDBScopeItem)it, 
						(ISVDBScopeItem)scope_new.getItems().get(
								scope_new.getItems().indexOf(it)),
						adds, removes, changes);
			}
			it.setParent(scope_ex);
			scope_ex.getItems().add(it);
		}
		
		return ret;
	}
}

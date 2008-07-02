package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBFileMerger {
	
	/**
	 * Merges changes in file2 back to file1 and collects info
	 * 
	 * @param file1
	 * @param file2
	 * @param adds
	 * @param removes
	 * @param changes
	 */
	public static void merge(
			SVDBFile			file1,
			SVDBFile			file2,
			List<SVDBItem>		adds,
			List<SVDBItem>		removes,
			List<SVDBItem>		changes) {
		merge_scope(file1, file2, adds, removes, changes);
	}
	
	private static int merge_scope(
			SVDBScopeItem		scope1,
			SVDBScopeItem		scope2,
			List<SVDBItem>		adds,
			List<SVDBItem>		removes,
			List<SVDBItem>		changes) {
		List<SVDBItem> temp = new ArrayList<SVDBItem>();
		int ret = 0;

		temp.clear();
		// Look for things that were added to scope2
		for (SVDBItem it_2 : scope2.getItems()) {
			if (!scope1.getItems().contains(it_2)) {
				if (adds != null) {
					adds.add(it_2);
				}
				temp.add(it_2);
			} else {
				temp.add(scope1.getItems().get(
						scope1.getItems().indexOf(it_2)));
			}
		}
		
		if (removes != null) {
			for (SVDBItem it_1 : scope1.getItems()) {
				if (!scope2.getItems().contains(it_1)) {
					removes.add(it_1);
				}
			}
		}
		
		scope1.getItems().clear();
		for (SVDBItem it : temp) {
			if (it instanceof SVDBScopeItem && scope2.getItems().contains(it)) {
				merge_scope((SVDBScopeItem)it, 
						(SVDBScopeItem)scope2.getItems().get(
								scope2.getItems().indexOf(it)),
						adds, removes, changes);
			}
			it.setParent(scope1);
			scope1.getItems().add(it);
		}
		
		return ret;
	}
}

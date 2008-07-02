package net.sf.sveditor.ui.explorer;

import java.text.Collator;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;

public class SVFileSorter extends ViewerSorter {

	public SVFileSorter() {
		// TODO Auto-generated constructor stub
	}

	public SVFileSorter(Collator collator) {
		super(collator);
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		if (e1 instanceof SVDBItem && e2 instanceof SVDBItem) {
			SVDBItem p1 = ((SVDBItem)e1).getParent();
			SVDBItem p2 = ((SVDBItem)e2).getParent();
			
			if (p1 != p2) {
				System.out.println("parents are not equal");
			}
		
			int i1 = ((SVDBScopeItem)p1).getItems().indexOf(e1);
			int i2 = ((SVDBScopeItem)p2).getItems().indexOf(e2);
			
			return (i1 - i2);
		}
		return super.compare(viewer, e1, e2);
	}

	@Override
	public void sort(Viewer viewer, Object[] elements) {
		System.out.println("SVFileSorter.sort()");
	}
}

package net.sf.sveditor.ui;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ITreeContentProvider;

public class ResourceSelCheckboxMgr implements ICheckStateListener {
	private boolean						fModifyingCheckState = false;
	private CheckboxTreeViewer			fTreeViewer;
	
	public ResourceSelCheckboxMgr(CheckboxTreeViewer tv) {
		fTreeViewer = tv;
	}
	
	public List<Object> getCheckedItems() {
		List<Object> ret = new ArrayList<Object>();
		
		for (Object o : fTreeViewer.getCheckedElements()) {
			if (!fTreeViewer.getGrayed(o)) {
				ret.add(o);
			}
		}
		
		return ret;
	}

	/**
	 * This method is invoked when auto-adding child elements to the selection.
	 * 
	 * @param parent
	 * @param elem
	 * @return
	 */
	protected boolean shouldIncludeInBlockSelection(Object parent, Object elem) {
		return true;
	}

	@Override
	public void checkStateChanged(CheckStateChangedEvent event) {
		if (fModifyingCheckState) {
			return;
		}
		
		ITreeContentProvider cp = (ITreeContentProvider)fTreeViewer.getContentProvider();
	
		try {
			fModifyingCheckState = true;
			boolean new_state_checked = event.getChecked();

			if (new_state_checked) {
				// Check elements below
				fTreeViewer.setGrayed(event.getElement(), false);
				set_checked_below(event.getElement(), true, cp);
			
				// Now, check up the stack to set the state appropriately
				Object parent, elem = event.getElement();
				boolean any_greyed=false;
				while ((parent = cp.getParent(elem)) != null) {
					// See if all the siblings of this 
					boolean has_siblings=false, all_siblings_checked=true;
					
					for (Object o : cp.getChildren(parent)) {
						has_siblings=true;
						if (!fTreeViewer.getChecked(o)) {
							all_siblings_checked=false;
						}
						any_greyed |= fTreeViewer.getGrayed(o);
					}
					
					if (has_siblings && all_siblings_checked) {
						fTreeViewer.setGrayed(parent, any_greyed);
						fTreeViewer.setChecked(parent, true);
					} else {
						fTreeViewer.setGrayChecked(parent, true);
					}
					elem = parent;
				}
			} else {
				// Un-check elements below
				set_checked_below(event.getElement(), false, cp);

				Object parent, elem = event.getElement();
				boolean any_greyed=false;
				while ((parent = cp.getParent(elem)) != null) {
					// See if all the siblings of this 
					boolean has_siblings=false, all_siblings_checked=true, any_siblings_checked=false;
					
					for (Object o : cp.getChildren(parent)) {
						has_siblings=true;
						if (!fTreeViewer.getChecked(o)) {
							all_siblings_checked = false;
						} else {
							any_siblings_checked = true;
						}
						any_greyed |= fTreeViewer.getGrayed(o);
					}
					
					if (has_siblings && all_siblings_checked) {
						fTreeViewer.setGrayed(parent, any_greyed);
						fTreeViewer.setChecked(parent, true);
					} else if (any_siblings_checked) {
						fTreeViewer.setGrayChecked(parent, true);
					} else {
						fTreeViewer.setGrayed(parent, false);
						fTreeViewer.setChecked(parent, false);
					}
					elem = parent;
				}
			}
		} finally {
			fModifyingCheckState = false;
		}
	}

	private void set_checked_below(Object elem, boolean checked, ITreeContentProvider cp) {
		boolean skipped = false;
		
		for (Object s : cp.getChildren(elem)) {
			boolean checked_s = checked;
			
			if (checked) {
				checked_s &= shouldIncludeInBlockSelection(elem, s);
				if (!checked_s) {
					skipped = true;
				}
			}
			fTreeViewer.setChecked(s, checked_s);
			if (cp.hasChildren(s)) {
				set_checked_below(s, checked, cp);
			}
		}
		
		if (checked && skipped) {
			fTreeViewer.setGrayed(elem, true);
		}
	}
}

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
package net.sf.sveditor.ui;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ITreeContentProvider;

public class ResourceSelCheckboxMgr implements ICheckStateListener {
	private boolean fModifyingCheckState = false;
	private CheckboxTreeViewer fTreeViewer;
	private LogHandle						fLog;
	private boolean debug = false;

	public ResourceSelCheckboxMgr(CheckboxTreeViewer tv) {
		fTreeViewer = tv;
		fLog = LogFactory.getLogHandle("ResourceSelCheckboxMgr");
	}

	public List<Object> getCheckedItems() {
		List<Object> ret = new ArrayList<Object>();

		// Grab all the checked elements
		Object ch[] = fTreeViewer.getCheckedElements();
		// Grab all the grayed elements
		List<Object> lgr = Arrays.asList(fTreeViewer.getGrayedElements());
		// Loop through all objects that are checked checking for those that
		// aren't grayed
		for (Object o : ch) {
			// Check if the list array of grayed elements contains the current
			// element...
			// if not add it to what we will be returning
			if (!lgr.contains(o)) {
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

		ITreeContentProvider cp = (ITreeContentProvider) fTreeViewer.getContentProvider();

		try {
			fModifyingCheckState = true;
			boolean new_state_checked = event.getChecked();

			long start = 0;
			if (debug)
				start = System.currentTimeMillis();
			if (new_state_checked) {
				// Check elements below
				fTreeViewer.setGrayed(event.getElement(), false);
				fTreeViewer.setSubtreeChecked(event.getElement(), true);
				if (set_checked_below(event.getElement(), true, cp))  {
					fTreeViewer.setGrayed(event.getElement(), true);
				}
				if (debug)
					fLog.note("set_checked - " + (System.currentTimeMillis()-start));

				// Now, check up the stack to set the state appropriately
				Object parent, elem = event.getElement();
				boolean any_greyed = false;
				while ((parent = cp.getParent(elem)) != null) {
					// See if all the siblings of this
					boolean has_siblings = false, all_siblings_checked = true;

					for (Object o : cp.getChildren(parent)) {
						has_siblings = true;
						if (!fTreeViewer.getChecked(o)) {
							all_siblings_checked = false;
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
				fTreeViewer.setSubtreeChecked(event.getElement(), false);
				set_checked_below(event.getElement(), false, cp);

				// Work way up tree, updating any parents that need an update
				Object parent, elem = event.getElement();
				boolean any_greyed = false;
				while ((parent = cp.getParent(elem)) != null) {
					// See if all the siblings of this
					boolean has_siblings = false, all_siblings_checked = true, any_siblings_checked = false;

					for (Object o : cp.getChildren(parent)) {
						has_siblings = true;
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
			if (debug)
				fLog.note("Time taken to parse hierarchy - " + (System.currentTimeMillis()-start));
		} finally {
			fModifyingCheckState = false;
		}
	}

	/**
	 * This function modifies the items checked.  It is assumed that all items have been checked or unchecked 
	 * before this function is called.
	 * 
	 * This function return true if the parent should be gray
	 * @param elem
	 * @param checked
	 * @param cp
	 * @return True if parent should be gray
	 */
	private boolean set_checked_below(Object elem, boolean checked, ITreeContentProvider cp) {
		boolean skipped = false;
		boolean make_parent_gray = false;

		for (Object s : cp.getChildren(elem)) {
			boolean checked_s = checked;

			if (checked) {
				checked_s &= shouldIncludeInBlockSelection(elem, s);
				if (!checked_s) {
					make_parent_gray = true;
					skipped = true;
					fTreeViewer.setChecked(s, false);
				}
			}
			if (cp.hasChildren(s)) {
				// If any child is gray, the parent will be gray too
				if (set_checked_below(s, checked, cp))  {
					make_parent_gray = true;
				}
			}
		}

		if (make_parent_gray) {
			fTreeViewer.setGrayed(elem, true);
		}
		return (make_parent_gray);
	}
}

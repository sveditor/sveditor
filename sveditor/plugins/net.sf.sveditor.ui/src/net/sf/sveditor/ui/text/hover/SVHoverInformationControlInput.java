/*******************************************************************************
 * Copyright (c) 2008, 2011 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed from JDT for use in SVEditor
 *******************************************************************************/
package net.sf.sveditor.ui.text.hover;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;




/**
 * Browser input for Javadoc hover.
 *
 * @since 3.4
 */
public class SVHoverInformationControlInput {
	
	public static final String							CONTENT_DECL = "Declaration";
	public static final String							CONTENT_DOC = "ContentDoc";
	public static final String							CONTENT_MACRO_EXP = "ContentMacroExpansion";
	
	private List<String>								fCycleOrder;
	private int											fCycleIdx;

	private Map<String, SVHoverContentProvider>			fContentProviders;

	private ISVDBScopeItem								fScope;
	private final ISVDBItemBase 						fElement;
	private ISVDBIndexIterator							fIndexIt;
//	private final String 								fHtml;
//	private final int 									fLeadingImageWidth;
	/**
	 * Creates a new browser information control input.
	 *
	 * @param previous previous input, or <code>null</code> if none available
	 * @param target the element, or <code>null</code> if none available
	 * @param html HTML contents, must not be null
	 * @param leadingImageWidth the indent required for the element image
	 */
//	public SVHoverInformationControlInput(SVHoverInformationControlInput previous, Tuple<ISVDBItemBase, SVDBFile> target, String html, int leadingImageWidth) {
	public SVHoverInformationControlInput(
			ISVDBItemBase 			element, 
			ISVDBScopeItem			scope,
			ISVDBIndexIterator 		index_it) {
		fScope   = scope;
		fElement = element;
		fIndexIt = index_it;
		
		fContentProviders = new HashMap<String, SVHoverContentProvider>();
		fCycleIdx = 0;
		
		fCycleOrder = new ArrayList<String>();
		fCycleOrder.add(CONTENT_DECL);
	}
	
	public ISVDBItemBase getElement() {
		return fElement;
	}
	
	public ISVDBScopeItem getScope() {
		return fScope;
	}
	
	public ISVDBIndexIterator getIndexIt() {
		return fIndexIt;
	}
	
	public int size() {
		return fContentProviders.size();
	}
	
	public void setCycleOrder(String order[]) {
		fCycleOrder.clear();
		fCycleIdx = 0;
		for (String o : order) {
			fCycleOrder.add(o);
		}
	}
	
	public String getContent() {
		String ret = null;
		
		for (int i=0; i<fCycleOrder.size(); i++) {
			if (fContentProviders.containsKey(fCycleOrder.get(fCycleIdx))) {
				ret = fContentProviders.get(fCycleOrder.get(fCycleIdx)).getContent(this);
				break;
			} else {
				fCycleIdx = ((fCycleIdx+1) % fCycleOrder.size());
			}
		}
		
		if (ret == null) {
			ret = "Default";
		}
	
		return ret;
	}
	
	public String getContent(String key) {
		if (fContentProviders.containsKey(key)) {
			return fContentProviders.get(key).getContent(this);
		} else {
			return null;
		}
	}
	
	public boolean hasContent(String key) {
		return fContentProviders.containsKey(key);
	}
	
	public String next() {
		fCycleIdx = ((fCycleIdx+1) % fCycleOrder.size());
	
		return getContent();
	}
	
	public void setContentProvider(String key, SVHoverContentProvider p) {
		if (fContentProviders.containsKey(key)) {
			fContentProviders.remove(key);
		}
		fContentProviders.put(key, p);
	}
	
	public SVHoverContentProvider getContentProvider(String key) {
		return fContentProviders.get(key);
	}
	
	/*
	 * @see org.eclipse.jface.internal.text.html.BrowserInput#getHtml()
	 */
//	public String getHtml() {
//		return fHtml;
//	}

	/*
	 * @see org.eclipse.jdt.internal.ui.infoviews.BrowserInput#getInputElement()
	 */
//	public Object getInputElement() {
//		return fElement == null ? (Object) fHtml : fElement;
//	}

	/*
	 * @see org.eclipse.jdt.internal.ui.infoviews.BrowserInput#getInputName()
	 */
//	public String getInputName() {
//		return fElement == null ? "" : "todo" ; 
//	}

}

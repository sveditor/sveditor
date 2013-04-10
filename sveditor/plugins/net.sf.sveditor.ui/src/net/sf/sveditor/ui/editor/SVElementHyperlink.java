/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed from JDT for use in SVEditor
 *******************************************************************************/

package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.db.ISVDBItemBase;

import org.eclipse.core.runtime.Assert;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.hyperlink.IHyperlink;


/**
 * SV element hyperlink.
 *
 * 
 */
public class SVElementHyperlink implements IHyperlink {

	private final IRegion fRegion;
	@SuppressWarnings("unused")
	private final ISVDBItemBase fElement;
	@SuppressWarnings("unused")
	private final boolean fQualify;
	private final Action fAction;
	private final String fLabel;

	public SVElementHyperlink(IRegion region, Action action, ISVDBItemBase element, boolean qualify, String label) {
		
		Assert.isNotNull(label) ;
		Assert.isNotNull(region) ;
		Assert.isNotNull(action) ;

		fRegion 	= region ;
		fElement	= element ;
		fQualify	= qualify ;
		fAction 	= action ;
		fLabel 		= label ;
	}

	public IRegion getHyperlinkRegion() {
		return fRegion;
	}

	public void open() {
		if(fAction != null) fAction.run() ;
	}

	public String getTypeLabel() {
		return fLabel;
	}

	public String getHyperlinkText() {
		return fLabel ;
	}
}

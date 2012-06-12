/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial contributor 
 ****************************************************************************/

package net.sf.sveditor.ui.views.diagram;

import org.eclipse.jface.viewers.LabelProvider;

public class AbstractDiagLabelProvider extends LabelProvider implements IDiagLabelProviderConfig {
	
	private boolean fIncludePrivateClassFields ;
	private boolean fIncludePublicClassFields ;
	private boolean fIncludePrivateClassTasksFunctions ;
	private boolean fIncludePublicClassTasksFunctions ; 
	private boolean fShowFieldTypes ;

	public boolean getIncludePrivateClassFields() {
		return fIncludePrivateClassFields ;
	}

	public boolean getIncludePublicClassFields() {
		return fIncludePublicClassFields ;
	}

	public boolean getIncludePrivateTasksFunctions() {
		return fIncludePrivateClassTasksFunctions ;
	}

	public boolean getIncludePublicTasksFunctions() {
		return fIncludePublicClassTasksFunctions ;
	}

	public void setIncludePrivateClassFields(boolean include) {
		fIncludePrivateClassFields = include ;
	}

	public void setIncludePublicClassFields(boolean include) {
		fIncludePublicClassFields = include ;
	}

	public void setIncludePrivateTasksFunctions(boolean include) {
		fIncludePrivateClassTasksFunctions = include ;
	}

	public void setIncludePublicTasksFunctions(boolean include) {
		fIncludePublicClassTasksFunctions = include ;
	}

	public boolean getShowFieldTypes() {
		return fShowFieldTypes ;
	}

	public void setShowFieldTypes(boolean show) {
		fShowFieldTypes = show ;
	}
}

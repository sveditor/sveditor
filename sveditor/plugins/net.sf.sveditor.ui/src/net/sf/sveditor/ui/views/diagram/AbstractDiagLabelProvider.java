/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Armond Paiva - initial contributor 
 ****************************************************************************/

package net.sf.sveditor.ui.views.diagram;

import org.eclipse.draw2d.AbstractRouter;
import org.eclipse.jface.viewers.LabelProvider;

public class AbstractDiagLabelProvider extends LabelProvider implements IDiagLabelProviderConfig {
	
	private boolean fIncludePrivateClassFields ;
	private boolean fIncludePublicClassFields ;
	private boolean fIncludePrivateClassTasksFunctions ;
	private boolean fIncludePublicClassTasksFunctions ; 
	private boolean fShowFieldTypes ;
	private AbstractRouter fRouter ;

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

	public void setSVDiagRouter(AbstractRouter router) {
		fRouter = router ;
	}
	
	public AbstractRouter getSVDiagRouter() {
		return fRouter ;
	}
	
}

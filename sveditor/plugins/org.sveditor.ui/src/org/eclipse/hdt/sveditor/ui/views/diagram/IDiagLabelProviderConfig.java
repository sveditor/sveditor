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

package org.sveditor.ui.views.diagram;

import org.eclipse.draw2d.AbstractRouter;

public interface IDiagLabelProviderConfig {
	
	boolean getIncludePrivateClassFields() ;
	
	boolean getIncludePublicClassFields() ;
	
	boolean getIncludePrivateTasksFunctions() ;
	
	boolean getIncludePublicTasksFunctions() ;
	
	boolean getShowFieldTypes() ;
	
	void setIncludePrivateClassFields(boolean include) ;
	
	void setIncludePublicClassFields(boolean include) ;
	
	void setIncludePrivateTasksFunctions(boolean include) ;
	
	void setIncludePublicTasksFunctions(boolean include) ;
	
	void setShowFieldTypes(boolean show) ;

	void setSVDiagRouter(AbstractRouter router);
	
}

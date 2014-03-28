/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial contributor 
 ****************************************************************************/

package net.sf.sveditor.ui.views.diagram;

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

/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.scanner;

import net.sf.sveditor.core.scanutils.ScanLocation;


public interface ISVScanner {
	
	void setStmtLocation(ScanLocation location);
	
	ScanLocation getStmtLocation();
	
	ScanLocation getStartLocation();

}

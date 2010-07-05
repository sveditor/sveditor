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


package net.sf.sveditor.core.log;

public interface ILogListener {
	int Type_Info  = 1;
	int Type_Debug = 2;
	int Type_Error = 4;
	
	void message(ILogHandle handle, int type, int level, String message);

}

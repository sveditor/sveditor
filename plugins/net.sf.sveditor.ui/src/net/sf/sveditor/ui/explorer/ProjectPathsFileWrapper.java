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


package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.core.db.SVDBFile;

import org.eclipse.core.runtime.IAdaptable;

public class ProjectPathsFileWrapper implements IAdaptable {
	private SVDBFile				fFile;
	
	public ProjectPathsFileWrapper(SVDBFile f) {
		fFile = f;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}

	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		if (adapter.equals(SVDBFile.class)) {
			return fFile;
		}
		return null;
	}
	
}

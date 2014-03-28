/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;

public class SVEditorDocumentProvider extends TextFileDocumentProvider {
	private static SVEditorDocumentProvider		fDefault;
	
	protected FileInfo createFileInfo(Object elem) throws CoreException {
		FileInfo result = super.createFileInfo(elem);
		
		setUpSynchronization(result);
		
		return result;
	}

	public static synchronized SVEditorDocumentProvider getDefault() {
		if (fDefault == null) {
			fDefault = new SVEditorDocumentProvider();
		}
		return fDefault;
	}
}

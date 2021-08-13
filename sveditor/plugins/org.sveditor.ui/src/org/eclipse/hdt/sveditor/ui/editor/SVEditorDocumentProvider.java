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
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.ui.editor;

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

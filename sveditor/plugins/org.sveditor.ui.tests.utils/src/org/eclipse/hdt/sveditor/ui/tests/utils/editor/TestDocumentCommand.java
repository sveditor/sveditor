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


package org.eclipse.hdt.sveditor.ui.tests.utils.editor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IDocument;

class TestDocumentCommand extends DocumentCommand {

	public TestDocumentCommand(int offset, int length, String text) {
		super();
		doit = true;
		this.text = text;

		this.offset = offset;
		this.length = length;

		owner = null;
		caretOffset = -1;
	}

	/**
	 * Returns new caret position.
	 */
	public int exec(IDocument doc) throws BadLocationException {
		doc.replace(offset, length, text);
		return caretOffset != -1 ?
					caretOffset :
					offset + (text == null ? 0 : text.length());
	}
}

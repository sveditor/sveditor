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


package net.sf.sveditor.ui.editor;

import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;

public interface ISVEditor {
	
	ISVDBIndexIterator getIndexIterator();
	
	IDocument getDocument();
	
	ITextSelection getTextSel();
	
	SVDBFile getSVDBFile();

}

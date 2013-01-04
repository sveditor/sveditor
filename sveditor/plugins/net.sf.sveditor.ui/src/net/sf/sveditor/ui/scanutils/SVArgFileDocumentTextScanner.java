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


package net.sf.sveditor.ui.scanutils;

import net.sf.sveditor.ui.argfile.editor.SVArgFileDocumentPartitions;

import org.eclipse.jface.text.IDocument;

public class SVArgFileDocumentTextScanner extends SVDocumentTextScannerBase {
	
	public SVArgFileDocumentTextScanner(
			IDocument 				doc,
			String					name,
			int						offset,
			boolean 				scan_fwd,
			boolean					skip_comments) {
		super(doc, SVArgFileDocumentPartitions.SV_ARGFILE_PARTITIONING,
				new String[] {
					SVArgFileDocumentPartitions.SV_ARGFILE_SINGLELINE_COMMENT,
					SVArgFileDocumentPartitions.SV_ARGFILE_MULTILINE_COMMENT},
				name, offset, scan_fwd, skip_comments);
	}
	
	public SVArgFileDocumentTextScanner(
			IDocument 				doc,
			int						offset) {
		this(doc, "", offset, true, false);
	}
	
	public SVArgFileDocumentTextScanner(
			IDocument 				doc,
			int						offset,
			int						limit) {
		this(doc, "", offset, true, false);
		fOffset = offset;
		fLimit  = limit;
	}
	
}

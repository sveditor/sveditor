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


package org.eclipse.hdt.sveditor.ui.scanutils;

import org.eclipse.hdt.sveditor.ui.argfile.editor.SVArgFileDocumentPartitions;

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

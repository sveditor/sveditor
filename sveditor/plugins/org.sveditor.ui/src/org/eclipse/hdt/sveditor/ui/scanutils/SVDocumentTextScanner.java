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

import org.eclipse.hdt.sveditor.ui.editor.SVDocumentPartitions;

import org.eclipse.jface.text.IDocument;

public class SVDocumentTextScanner extends SVDocumentTextScannerBase {
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			String					name,
			int						offset,
			boolean 				scan_fwd,
			boolean					skip_comments) {
		super(doc, SVDocumentPartitions.SV_PARTITIONING, 
				new String[] {
					SVDocumentPartitions.SV_MULTILINE_COMMENT,
					SVDocumentPartitions.SV_SINGLELINE_COMMENT},
				name, offset, scan_fwd, skip_comments);
	}
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			String					partitioning,
			String					comment_partitions[],
			String					name,
			int						offset,
			boolean 				scan_fwd,
			boolean					skip_comments) {
		super(doc, partitioning, comment_partitions,
				name, offset, scan_fwd, skip_comments);
	}
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			int						offset) {
		this(doc, "", offset, true, false);
	}
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			int						offset,
			int						limit) {
		this(doc, "", offset, true, false);
		fOffset = offset;
		fLimit  = limit;
	}
	
}

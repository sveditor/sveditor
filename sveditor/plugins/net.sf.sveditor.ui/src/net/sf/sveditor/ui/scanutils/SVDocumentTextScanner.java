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


package net.sf.sveditor.ui.scanutils;

import net.sf.sveditor.ui.editor.SVDocumentPartitions;

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

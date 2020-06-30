/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.ui.compare;

import org.eclipse.hdt.sveditor.ui.editor.SVDocumentPartitions;
import org.eclipse.hdt.sveditor.ui.editor.SVDocumentSetupParticipant;
import org.eclipse.hdt.sveditor.ui.editor.SVSourceViewerConfiguration;

import org.eclipse.compare.CompareConfiguration;
import org.eclipse.compare.contentmergeviewer.TextMergeViewer;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;

public class SVCompareViewer extends TextMergeViewer {

	public SVCompareViewer(Composite parent, CompareConfiguration configuration) {
		super(parent, SWT.LEFT_TO_RIGHT, configuration);
	}
	
	@Override
	protected void configureTextViewer(TextViewer textViewer) {
		if(textViewer instanceof SourceViewer) {
			SourceViewer viewer = (SourceViewer)textViewer;
			SVSourceViewerConfiguration configuration = new SVSourceViewerConfiguration(null,null);
			viewer.configure(configuration);
		}
	}

	@Override
	protected IDocumentPartitioner getDocumentPartitioner() {
		return SVDocumentSetupParticipant.createPartitioner();
	}

	@Override
	protected String getDocumentPartitioning() {
		return SVDocumentPartitions.SV_PARTITIONING;
	}
	
}

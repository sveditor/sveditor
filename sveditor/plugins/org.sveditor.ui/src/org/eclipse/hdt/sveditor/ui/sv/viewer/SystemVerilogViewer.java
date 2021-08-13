/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.sv.viewer;

import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.AnnotationModel;
import org.eclipse.jface.text.source.CompositeRuler;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.TextSourceViewerConfiguration;
import org.eclipse.ui.internal.editors.text.EditorsPlugin;
import org.eclipse.ui.texteditor.AnnotationPreference;
import org.eclipse.ui.texteditor.DefaultMarkerAnnotationAccess;
import org.eclipse.ui.texteditor.SourceViewerDecorationSupport;

import org.eclipse.hdt.sveditor.ui.editor.SVCodeScanner;
import org.eclipse.hdt.sveditor.ui.editor.SVDocumentPartitions;
import org.eclipse.hdt.sveditor.ui.editor.SVDocumentSetupParticipant;

public class SystemVerilogViewer extends SourceViewer {
	protected Document							fDocument;
	protected SourceViewerDecorationSupport		fDecorationSupport;
	
	public SystemVerilogViewer(Composite parent, int style) {
		super(parent, new CompositeRuler(), null, true, style);
		getTextWidget().setFont(
				JFaceResources.getFont(JFaceResources.TEXT_FONT));
		
		fDocument = new Document("");
		IDocumentPartitioner p = SVDocumentSetupParticipant.createPartitioner();
		fDocument.setDocumentPartitioner(SVDocumentPartitions.SV_PARTITIONING, p);
		p.connect(fDocument);
	
		setDocument(fDocument, new AnnotationModel());
		configure(new SourceViewerConfig());
		
		fDecorationSupport = new SourceViewerDecorationSupport(
				this, null, new DefaultMarkerAnnotationAccess(), 
				EditorsPlugin.getDefault().getSharedTextColors());
		configureSourceViewerDecorationSupport();
//		fDecorationSupport.setAnnotationPreference(
//				new AnnotationPreference("org.eclipse.ui.workbench.texteditor.error", 
//						"red", "editorKey", "overviewKey", 0));
//		fDecorationSupport.install(null);
	}
	
	protected void configureSourceViewerDecorationSupport() {
		fDecorationSupport.setSymbolicFontName(JFaceResources.TEXT_FONT);
	}
	
	public void setContent(String content) {
		fDocument.set(content);
	}
	
	class SourceViewerConfig extends TextSourceViewerConfiguration {
		private SVCodeScanner			fScanner;
		
		public SourceViewerConfig() {
			fScanner = new SVCodeScanner(null);
		}
		
		public void setContentType(IContentType ct) {
			fScanner.updateRules(ct);
		}
		
		public SVCodeScanner getScanner() {
			return fScanner;
		}
		
		@Override
		public IReconciler getReconciler(ISourceViewer sourceViewer) {
			// TODO Auto-generated method stub
			return super.getReconciler(sourceViewer);
		}

		@Override
		public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) {
			PresentationReconciler rec = new PresentationReconciler();
			rec.setDocumentPartitioning(
					getConfiguredDocumentPartitioning(sourceViewer));
			
			DefaultDamagerRepairer dr = new DefaultDamagerRepairer(fScanner);

			rec.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
			rec.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
			for (String p : SVDocumentPartitions.SV_PARTITION_TYPES) {
				rec.setDamager(dr, p);
			}
		
			return rec;
		}
		
		@Override
		public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {
			return new String[] {
					IDocument.DEFAULT_CONTENT_TYPE,
					SVDocumentPartitions.SV_MULTILINE_COMMENT,
					SVDocumentPartitions.SV_SINGLELINE_COMMENT,
					SVDocumentPartitions.SV_STRING,
					SVDocumentPartitions.SV_KEYWORD
			};
		}

		@Override
		public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer) {
			return SVDocumentPartitions.SV_PARTITIONING;
		}
	}

}

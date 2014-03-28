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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension4;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ISynchronizable;
import org.eclipse.jface.text.reconciler.DirtyRegion;
import org.eclipse.jface.text.reconciler.IReconcilingStrategy;
import org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension;

public class SVReconcilingStrategy implements IReconcilingStrategy,
		IReconcilingStrategyExtension {
	private IDocument				fDocument;
	private SVEditor				fEditor;
	
	public SVReconcilingStrategy(SVEditor editor) {
		fEditor = editor;
	}

	
	public void reconcile(IRegion partition) {
		reconcileSource();
		if (fEditor != null) {
			fEditor.updateSVDBFile(fDocument, false);
		}
	}

	
	public void reconcile(DirtyRegion dirtyRegion, IRegion subRegion) {
		reconcileSource();
		if (fEditor != null) {
			fEditor.updateSVDBFile(fDocument, false);
		}
	}

	
	public void setDocument(IDocument document) {
		fDocument = document;
	}

	
	public void initialReconcile() {
		reconcileSource();
		if (fEditor != null) {
			fEditor.updateSVDBFile(fDocument, true);
		}
	}
	
	public void setProgressMonitor(IProgressMonitor monitor) {}

	private Object getLockObject() {
		if (fDocument instanceof ISynchronizable) {
			Object lock = ((ISynchronizable)fDocument).getLockObject();
			
			if (lock != null) {
				return lock;
			}
		}
		return fDocument;
	}
	
	private void reconcileSource() {
		if (fDocument != null) {
			/*
			long modTS;
			String content;
			 */
			
			synchronized(getLockObject()) {
				/* content = */ fDocument.get();
				
				/* modTS = */ ((IDocumentExtension4)fDocument).getModificationStamp();
			}
		}
		
	}
}

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
package org.sveditor.ui.script.launch;

import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.ui.console.IConsoleHyperlink;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;

public class ExternalPathHyperlink implements IConsoleHyperlink {
	private IFileStore				fFile;
	private String					fEditorId;
	private int						fOffset;
	private int						fLength;
	private int						fLineno;
	
	public ExternalPathHyperlink(
			IFileStore				file,
			String					editor_id,
			int						offset,
			int						length,
			int						lineno
			) {
		fFile = file;
		fEditorId = editor_id;
		fOffset = offset;
		fLength = length;
		fLineno = lineno;
	}

	@Override
	public void linkEntered() { }

	@Override
	public void linkExited() { }

	@Override
	public void linkActivated() {
		IWorkbenchWindow window = DebugUIPlugin.getActiveWorkbenchWindow();
		if (window != null) {
			IWorkbenchPage page = window.getActivePage();
			if (page != null) {
				try {
					IEditorPart editorPart = IDE.openInternalEditorOnFileStore(page, fFile);
//					IEditorPart editorPart = page.openEditor(new FileEditorInput(fFile), getEditorId() , true);
					if (fLineno > 0) {
						ITextEditor textEditor = null;
						if (editorPart instanceof ITextEditor) {
							textEditor = (ITextEditor) editorPart;
						} else {
							textEditor = (ITextEditor) editorPart.getAdapter(ITextEditor.class);
						}
						if (textEditor != null) {
							IEditorInput input = editorPart.getEditorInput();
							if (fOffset < 0) {
								IDocumentProvider provider = textEditor.getDocumentProvider();
								try {
									provider.connect(input);
								} catch (CoreException e) {
									// unable to link
									DebugUIPlugin.log(e);
									return;
								}
								IDocument document = provider.getDocument(input);
								try {
	                                IRegion region= document.getLineInformation(fLineno - 1);
									fOffset = region.getOffset();
									fLength = region.getLength();
								} catch (BadLocationException e) {
									// unable to link
									DebugUIPlugin.log(e);
								}
								provider.disconnect(input);
							}
							if (fOffset >= 0 && fLength >=0) {
								textEditor.selectAndReveal(fOffset, fLength);
							}
						}
					}
				} catch (PartInitException e) {
					DebugUIPlugin.log(e);
				}	
			}
		}				
	}

}

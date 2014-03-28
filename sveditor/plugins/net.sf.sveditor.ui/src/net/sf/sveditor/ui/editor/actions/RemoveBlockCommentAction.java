/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Eclipse CDT -- initial implementation
 ****************************************************************************/

package net.sf.sveditor.ui.editor.actions;

import java.util.LinkedList;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.ui.editor.SVDocumentPartitions;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITypedRegion;

public class RemoveBlockCommentAction extends BlockCommentAction {
	
	public RemoveBlockCommentAction(ResourceBundle bundle, String prefix, SVEditor editor) {
		super(bundle, prefix, editor);
	}
	
	/*
	 * @see org.eclipse.jdt.internal.ui.actions.AddBlockCommentAction#runInternal(org.eclipse.jface.text.ITextSelection, org.eclipse.jface.text.IDocumentExtension3, org.eclipse.jdt.internal.ui.actions.AddBlockCommentAction.Edit.EditFactory)
	 */
	protected void runInternal(ITextSelection selection, IDocumentExtension3 docExtension, Edit.EditFactory factory) throws BadPartitioningException, BadLocationException {
		List<Edit> edits= new LinkedList<Edit>();
		int tokenLength= getCommentStart().length();
		
		int offset= selection.getOffset();
		int endOffset= offset + selection.getLength();

		ITypedRegion partition= docExtension.getPartition(SVDocumentPartitions.SV_PARTITIONING, offset, false);
		int partOffset= partition.getOffset();
		int partEndOffset= partOffset + partition.getLength();
		
		while (partEndOffset < endOffset) {
			
			if (partition.getType() == SVDocumentPartitions.SV_MULTILINE_COMMENT) {
				edits.add(factory.createEdit(partOffset, tokenLength, "")); //$NON-NLS-1$
				edits.add(factory.createEdit(partEndOffset - tokenLength, tokenLength, "")); //$NON-NLS-1$
			}
			
			partition= docExtension.getPartition(SVDocumentPartitions.SV_PARTITIONING, partEndOffset, false);
			partOffset= partition.getOffset();
			partEndOffset= partOffset + partition.getLength();
		}

		if (partition.getType() == SVDocumentPartitions.SV_MULTILINE_COMMENT) {
			edits.add(factory.createEdit(partOffset, tokenLength, "")); //$NON-NLS-1$
			edits.add(factory.createEdit(partEndOffset - tokenLength, tokenLength, "")); //$NON-NLS-1$
		}

		executeEdits(edits);
	}

	/*
	 * @see org.eclipse.jdt.internal.ui.actions.AddBlockCommentAction#validSelection(org.eclipse.jface.text.ITextSelection)
	 */
	protected boolean isValidSelection(ITextSelection selection) {
		return selection != null && !selection.isEmpty() && selection.getLength() > 0;
	}

}

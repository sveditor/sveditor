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

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultIndentLineAutoEditStrategy;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextUtilities;

public class SVMultiLineCommentAutoIndentStrategy extends
		DefaultIndentLineAutoEditStrategy {

    private final String 				fPartitioning;

    public SVMultiLineCommentAutoIndentStrategy(String partitioning) {
        fPartitioning = partitioning;
    }


    /**
     * Gets the range of the multi-line comment prefix on a document
     * line.  The prefix matches any number of whitespace characters
     * followed by an asterisk followed by any number of whitespace
     * characters.
     * @return  a regions describing the range of the prefix on the 
     *          line.
     * @throws  BadLocationException if accessing the document fails.
     */
    private IRegion findPrefixRange(IDocument doc, IRegion line) 
    	throws BadLocationException {
    	
        int lineOffset = line.getOffset();
        int lineEnd = lineOffset + line.getLength();
        int indentEnd = findEndOfWhiteSpace(doc, lineOffset, lineEnd);
        
        if ((indentEnd < lineEnd) && (doc.getChar(indentEnd) == '*')) {
            indentEnd++;
            while ((indentEnd < lineEnd) && 
                    Character.isWhitespace(doc.getChar(indentEnd))) {
                indentEnd++;
            }
        }
        return new Region(lineOffset, indentEnd - lineOffset);
    }

    /**
     * Tests whether the comment partition is likely to be closed
     * 
     * @param doc
     * @param offset
     * @return
     */
    private boolean isCommentClosed(IDocument doc, int offset) {
        try {
        	// End of document, so the comment must not be closed
            if ((doc.getLineOfOffset(offset) + 1) >= doc.getNumberOfLines()) {
                return false;
            }
            
            IRegion line = doc.getLineInformation(doc.getLineOfOffset(offset)+1);
            ITypedRegion partition = TextUtilities.getPartition(
                    doc, fPartitioning, offset, false);
            int partitionEnd = partition.getOffset() + partition.getLength();
            if (line.getOffset() >= partitionEnd) {
            	// The next line is in a different partition, so the comment
            	// must already be closed
                return true;
            }
            if (doc.getLength() == partitionEnd) {
            	// The comment partition goes to the end of the document, so
            	// the comment is unlikely to be closed
                return false;
            }
            
            String comment = doc.get(partition.getOffset(), partition.getLength());
            if (comment.indexOf("/*", 2) != -1) {
            	// There's another start-comment in this comment partition,
            	// so it's unlikely to be closed
                return false;
            }
            
            // likely closed already 
            return true;
        } catch (BadLocationException e) {
        	// give up and claim that we have a closed comment
            return true;
        }
    }

    /**
     * Continues the comment on the next line
     */
    private void addIndentAndContinueComment(IDocument doc, DocumentCommand cmd) {
        int offset = cmd.offset;
        
        if ((offset == -1) || (doc.getLength() == 0)) {
            return;
        }
        
        try {
            IRegion line = doc.getLineInformationOfOffset(
            		(offset==doc.getLength())?(offset-1):offset);
            
            int lineOffset = line.getOffset();
            int firstNonWS = findEndOfWhiteSpace(doc, lineOffset, offset);
            
            StringBuilder buf = new StringBuilder(cmd.text);
            IRegion prefix = findPrefixRange(doc, line);
            
            String indent = doc.get(prefix.getOffset(), prefix.getLength());
            int lenToAdd = 
                Math.min(offset - prefix.getOffset(), prefix.getLength());
            
            buf.append(indent.substring(0, lenToAdd));
            if (firstNonWS < offset) {
                if (doc.getChar(firstNonWS) == '/') {
                	// The previous line was the comment start, so we must
                	// add an extra space and star on this line
                    buf.append(" * ");
                }
            }
            
            if (!isCommentClosed(doc, offset)) {
                cmd.shiftsCaret = false;
                cmd.caretOffset = cmd.offset + buf.length();
                String lineDelimiter = TextUtilities.getDefaultLineDelimiter(doc);
                String endTag = lineDelimiter + indent + " */";
                buf.append(endTag);
            }
            
            // move caret behind prefix.
            if (lenToAdd < prefix.getLength()) {
                cmd.caretOffset = offset + prefix.getLength() - lenToAdd;
            }
            cmd.text = buf.toString();
        } catch (BadLocationException e) {
        }
    }

    public void customizeDocumentCommand(IDocument doc, DocumentCommand cmd) {
        // TODO Test for smart mode.
        if (cmd.text != null) {
            // No auto-indent if replacing existing characters.
            if (cmd.length == 0 && cmd.text.length() == 1) {
                String[] lineDelimiters = doc.getLegalLineDelimiters();
                int index = TextUtilities.endsWith(lineDelimiters, cmd.text);
                if ((index >= 0) && lineDelimiters[index].equals(cmd.text)) {
                    // entered text is just a line feed, so do
                    // auto-indent now.
                    addIndentAndContinueComment(doc, cmd);
                }
            }
            // TODO - if slash entered, remove auto inserted space since last star.
            // JDT implementation seems a little lame, should maintain
            // state about how much whitespace was auto-inserted.
        }
    }

}

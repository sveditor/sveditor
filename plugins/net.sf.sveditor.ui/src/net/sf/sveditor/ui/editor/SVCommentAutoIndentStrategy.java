package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultIndentLineAutoEditStrategy;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextUtilities;

public class SVCommentAutoIndentStrategy extends
		DefaultIndentLineAutoEditStrategy {

    private final String partitioning;

    public SVCommentAutoIndentStrategy(String partitioning) {
        this.partitioning = partitioning;
    }

    /**
     * Copies the indentation of the previous line and adds a star.
     */
    private void indentAfterNewLine(IDocument doc, DocumentCommand cmd) {
        int offset = cmd.offset;
        if ((offset == -1) || (doc.getLength() ==0)) {
            return;
        }
        
        try {
            int pos = (offset == doc.getLength()) ? offset - 1 : offset;
            IRegion line = doc.getLineInformationOfOffset(pos);
            
            int lineOffset = line.getOffset();
            int firstNonWS = findEndOfWhiteSpace(doc, lineOffset, offset);
            
            StringBuffer buf = new StringBuffer(cmd.text);
            IRegion prefix = findPrefixRange(doc, line);
            String indentation = 
                doc.get(prefix.getOffset(), prefix.getLength());
            int lenToAdd = 
                Math.min(offset - prefix.getOffset(), prefix.getLength());
            
            buf.append(indentation.substring(0, lenToAdd));
            if (firstNonWS < offset) {
                if (doc.getChar(firstNonWS) == '/') {
                    // Comment started on previous line so space past
                    // the slash position before inserting star.
                    buf.append(" * ");
                }
            }
            
            // TODO test for preference before closing the comment.
            if (isNewComment(doc, offset)) {
                cmd.shiftsCaret = false;
                cmd.caretOffset = cmd.offset + buf.length();
                String lineDelimiter =
                    TextUtilities.getDefaultLineDelimiter(doc);
                String endTag = lineDelimiter + indentation + " */";
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

    /**
     * Gets the range of the multi-line comment prefix on a document
     * line.  The prefix matches any number of whitespace characters
     * followed by an asterisk followed by any number of whitespace
     * characters.
     * @return  a regions describing the range of the prefix on the 
     *          line.
     * @throws  BadLocationException if accessing the document fails.
     */
    private IRegion findPrefixRange(IDocument doc, IRegion line) throws BadLocationException {
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
    
    private boolean isNewComment(IDocument doc, int offset) {
        try {
            int lineIndex = doc.getLineOfOffset(offset) + 1;
            if (lineIndex >= doc.getNumberOfLines()) {
                // No additional lines so must need to close the
                // comment.
                return true;
            }
            IRegion line = doc.getLineInformation(lineIndex);
            ITypedRegion partition = TextUtilities.getPartition(
                    doc, partitioning, offset, false);
            int partitionEnd = partition.getOffset() + partition.getLength();
            if (line.getOffset() >= partitionEnd) {
                // Next line is a different partition, so must have
                // already closed the comment.
                return false;
            }
            if (doc.getLength() == partitionEnd) {
                // Partition goes to end of document - probably new.
                return true;
            }
            String comment = doc.get(partition.getOffset(), partition.getLength());
            if (comment.indexOf("/*", 2) != -1) {
                // Encloses another comment - probably new.
                return true;
            }
            return false;
        } catch (BadLocationException e) {
            return false;
        }
    }

    public void customizeDocumentCommand(IDocument doc, DocumentCommand cmd) {
    	System.out.println("customizeDocumentCommand: \"" + cmd.text + "\"");
        // TODO Test for smart mode.
        if (cmd.text != null) {
            // No auto-indent if replacing existing characters.
            if (cmd.length == 0) {
                String[] lineDelimiters = doc.getLegalLineDelimiters();
                int index = TextUtilities.endsWith(lineDelimiters, cmd.text);
                if ((index >= 0) && lineDelimiters[index].equals(cmd.text)) {
                    // entered text is just a line feed, so do
                    // auto-indent now.
                    indentAfterNewLine(doc, cmd);
                }
            }
            // TODO - if slash entered, remove auto inserted space since last star.
            // JDT implementation seems a little lame, should maintain
            // state about how much whitespace was auto-inserted.
        }
    }

}

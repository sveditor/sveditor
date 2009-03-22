package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.scanner.SVKeywords;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultIndentLineAutoEditStrategy;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextUtilities;

public class SVAutoIndentStrategy extends DefaultIndentLineAutoEditStrategy {
	
	private final String				fParititioning;
	
	public SVAutoIndentStrategy(String p) {
		fParititioning = p;
	}

    public void customizeDocumentCommand(IDocument doc, DocumentCommand cmd) {
    	System.out.println("SVAutoIndentStrategy: cmd=" + cmd.text);
    	
        String[] lineDelimiters = doc.getLegalLineDelimiters();
        int index = TextUtilities.endsWith(lineDelimiters, cmd.text);
        if ((index >= 0) && lineDelimiters[index].equals(cmd.text)) {
        	System.out.println("indent trigger");
        	
        	// Scan backwards
        	int idx = cmd.offset;
        	try {
        		while (idx >= 0 && Character.isWhitespace(doc.getChar(idx))) {
        			idx--;
        		}
        		
        		if (doc.getChar(idx) == ';') {
        			// what kind of statement do we have?
        			
        			// Find the last identifier, excluding items in parens
        			while (idx >= 0) {
        				while (idx >= 0 && Character.isWhitespace(doc.getChar(idx))) {
        					idx--;
        				}

        				if (idx >= 0) {
        					if (doc.getChar(idx) == ')') {
        						int match = 0;

        						int start = idx;
        						do {
        							int ch = doc.getChar(idx);

        							if (ch == ')') {
        								match++;
        							} else if (ch == '(') {
        								match--;
        							}
        							idx--;
        						} while (idx >= 0 && match != 0);

        						String expr = doc.get(idx+1, (start-idx+1));

        						System.out.println("expr=" + expr);
        					} else if (Character.isJavaIdentifierPart(doc.getChar(idx))) {
        						// Read an idenfitier
        						int start = idx;

        						while (Character.isJavaIdentifierPart(doc.getChar(idx))) {
        							idx--;
        						}

        						String id = doc.get(idx+1, (start-idx));
        						
        						System.out.println("id=\"" + id + "\"");

        						if (SVKeywords.isSVKeyword(id) &&
        								!SVKeywords.isBuiltInType(id)) {
        							System.out.println("is keyword: " + id);
        							break;
        						}
        					} else {
        						System.out.println("UNKOWN: " + doc.getChar(idx));
        						idx--;
        					}
        				}
        			}
        		} else {
        			int start = idx;
        			// Now, search back to another whitespace char
        		
        			idx--;
        			while (idx >= 0) {
        				if (Character.isWhitespace(doc.getChar(idx))) {
        					break;
        				}
        				idx--;
        			}
            		String str = doc.get(idx+1, start-idx+1);
            		System.out.println("str=" + str);
            		
            		if (SVKeywords.isSVKeyword(str) && str.startsWith("end")) {
            			// indent in-line with the preceeding 'end'
            	    	super.customizeDocumentCommand(doc, cmd);
            		}
        		}
        		
        	} catch (BadLocationException e) {
        		e.printStackTrace();
        	}
        }

        // Default handling
    	super.customizeDocumentCommand(doc, cmd);
    }
}

package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.utils.SVDBFileSearcher;
import net.sf.sveditor.core.scanner.SVTaskFuncParam;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;

public class SVCompletionProcessor implements IContentAssistProcessor {
	
	private SVEditor			fEditor;
	
	private static final char[] PROPOSAL_ACTIVATION_CHARS =
	{'.', ':'};
	
	private final ICompletionProposal NO_COMPLETIONS[] = 
		new ICompletionProposal[0];
	private final IContextInformation NO_CONTEXTS[] = 
		new IContextInformation[0];
	
	public void init(SVEditor editor) {
		fEditor = editor;
	}

	
	public ICompletionProposal[] computeCompletionProposals(
			ITextViewer viewer, int offset) {
		if (true) {
			return NO_COMPLETIONS;
		}
		
		List<ICompletionProposal> ret = new ArrayList<ICompletionProposal>();
	    int docOffset = offset - 1;
	    
	    try {
	      while (((docOffset) >= viewer.getTopIndexStartOffset())
	          && Character.isLetterOrDigit(viewer.getDocument()
	              .getChar(docOffset))) {
	        docOffset--;
	      }
	      
	      //we've been one step too far : increase the offset
	      int trigger_ch = viewer.getDocument().getChar(docOffset);
	      
	      String trigger = "";
	      if (trigger_ch == ':') {
	    	  if (viewer.getDocument().getChar(docOffset-1) != ':') {
	    		  return NO_COMPLETIONS;
	    	  }
	    	  trigger = "::";
	      } else {
	    	  trigger = "" + trigger_ch;
	      }
	      
	      docOffset++;
	      
	      // Find the line where we're inserting
	      int lineno = viewer.getDocument().getLineOfOffset(docOffset);
	      String wordPart = viewer.getDocument().get(docOffset,
	          offset - docOffset);
	      
	      System.out.println("wordPart=" + wordPart + " trigger=" + trigger);
	      
	      SVDBFileSearcher s = new SVDBFileSearcher(fEditor.getSVDBFile());
	      SVDBScopeItem scope = s.findActiveScope(lineno);
	      
	      if (scope != null) {
	    	  if (scope instanceof SVDBTaskFuncScope) {
	    		  // behavioral scope. 
	    		  // If no root, then see if there is a prefix
	    		  // If a root, find the type and go from there...
	    		  for (SVDBItem it : scope.getItems()) {
	    			  if (it instanceof SVDBVarDeclItem ||
	    					  it instanceof SVDBTaskFuncParam) {
	    				  CompletionProposal p = new CompletionProposal(
	    						  it.getName(), offset, 
	    						  it.getName().length(), 0);
	    				  ret.add(p);
	    			  }
	    		  }
	    		  for (SVDBItem it : scope.getParent().getItems()) {
	    			  if (it instanceof SVDBVarDeclItem ||
	    					  it instanceof SVDBTaskFuncScope) {
	    				  CompletionProposal p = new CompletionProposal(
	    						  it.getName(), offset, 
	    						  it.getName().length(), 0);
	    				  ret.add(p);
	    			  }
	    		  }
	    	  } else if (scope instanceof SVDBModIfcClassDecl) {
	    		  // structural scope. Prompt with type names and keywords
	    		  for (SVDBItem it : scope.getItems()) {
	    			  if (it instanceof SVDBVarDeclItem) {
	    				  SVDBVarDeclItem v_it = (SVDBVarDeclItem)it;
	    				  CompletionProposal p = new CompletionProposal(
	    						  v_it.getName(), offset, 
	    						  v_it.getName().length(), 0);
	    				  ret.add(p);
	    			  }
	    		  }
	    	  }
	    	  System.out.println("scope=" + scope);
	      }
	    } catch (BadLocationException e) {
	      // do nothing
	    }
		
		System.out.println("computeCompletionProposals()");
		
		// Find the start point
		int start = offset;
		
		String pre = null;
		try {
			while (start >= 0) {
				int ch = viewer.getDocument().getChar(start); 
				if (Character.isWhitespace(ch) || ch == '.') {
					break;
				}
				start--;
			}
			pre = viewer.getDocument().get(start, (offset-start));
		} catch (BadLocationException e ) {
		}
		
		System.out.println("pre=" + pre);
		CompletionProposal p = new CompletionProposal("foo", offset, 3, 0);
		CompletionProposal p1 = new CompletionProposal(
				"foo2", offset, 4, 0);

		return ret.toArray(new ICompletionProposal[ret.size()]);
	}

	
	public IContextInformation[] computeContextInformation(
			ITextViewer viewer, int offset) {
		System.out.println("computeContextInformation()");
		return NO_CONTEXTS;
	}

	
	public char[] getCompletionProposalAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	
	public char[] getContextInformationAutoActivationCharacters() {
		System.out.println("getContextInformationAutoActivationCharacters");
		return null;
	}

	
	public IContextInformationValidator getContextInformationValidator() {
		System.out.println("getContextInformationValidator()");
		// TODO Auto-generated method stub
		return null;
	}

	
	public String getErrorMessage() {
		// TODO Auto-generated method stub
		return null;
	}

}

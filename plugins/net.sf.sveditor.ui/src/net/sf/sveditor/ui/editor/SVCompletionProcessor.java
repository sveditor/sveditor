package net.sf.sveditor.ui.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.utils.SVDBFileSearcher;
import net.sf.sveditor.core.scanner.SVTaskFuncParam;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
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
		System.out.println("computeCompletionProposals");
		
		SVDBProjectManager pm = SVCorePlugin.getDefault().getProjMgr();
		File file = fEditor.getFilePath();
		
		IFile files[] = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(file.toURI());
		List<SVDBModIfcClassDecl> classes = new ArrayList<SVDBModIfcClassDecl>();
		
		if (files != null && files.length > 0) {
			SVDBProjectData pd = pm.getProjectData(files[0].getProject());
		
			// Just for kicks, look for all class definitions
			for (SVDBFile f : pd.getFileIndex().getFileList()) {

				for (SVDBItem it : f.getItems()) {
					if (it.getType() == SVDBItemType.Class) {
						classes.add((SVDBModIfcClassDecl)it);
					}
				}
			}
		}
		
		/*
		if (true) {
			return NO_COMPLETIONS;
		}
		 */
		
		List<ICompletionProposal> ret = new ArrayList<ICompletionProposal>();
	    int docOffset = offset - 1;
        int replacement_length = 0;
		// Find the start point
		int start = docOffset;
		String pre = null;
		
		try {
			while (start >= 0) {
				int ch = viewer.getDocument().getChar(start);
				System.out.println("ch=" + (char)ch);
				if (Character.isWhitespace(ch) || ch == '.') {
					start++;
					break;
				}
				start--;
			}
			pre = viewer.getDocument().get(start, (offset-start));
		} catch (BadLocationException e ) {
			e.printStackTrace();
		}
		
		start++;
		
		replacement_length = docOffset - start;
		
		System.out.println("pre=" + pre);
	    
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
	    	  trigger = "" + (char)trigger_ch;
	      }
	      
	      docOffset++;
	      
	      // Find the line where we're inserting
	      int lineno = viewer.getDocument().getLineOfOffset(docOffset);
	      String wordPart = viewer.getDocument().get(docOffset,
	          offset - docOffset);
	      
	      // TODO: CompletionProposal parameters are:
	      // replacementString
	      // replacementOffset
	      // replacementLength (number of characters to replace)
	      // cursorEndPos (relative to replacementOffset)
	      //
	      // We need to correctly compute replacementLength and cursorEndPos
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
	    						  replacement_length, 0);
	    				  ret.add(p);
	    			  }
	    		  }
	    		  for (SVDBItem it : scope.getParent().getItems()) {
	    			  if (it instanceof SVDBVarDeclItem ||
	    					  it instanceof SVDBTaskFuncScope) {
	    				  CompletionProposal p = new CompletionProposal(
	    						  it.getName(), offset, 
	    						  replacement_length, 0);
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
	    						  replacement_length, 0);
	    				  ret.add(p);
	    			  }
	    		  }
	    	  }
	    	  System.out.println("scope=" + scope);
	      }
	    } catch (BadLocationException e) {
	      // do nothing
	    }
	    
	    System.out.println("start=" + start + " offset=" + offset + " replacement_length=" + replacement_length);
	    for (SVDBModIfcClassDecl c : classes) {
	    	if (pre != "") {
	    		if (c.getName().startsWith(pre)) {
		    		CompletionProposal p = new CompletionProposal(
		    				c.getName(), start /* offset */, 
		    				replacement_length+1, c.getName().length());
		    		ret.add(p);
	    		}
	    	} else {
	    		CompletionProposal p = new CompletionProposal(
	    				c.getName(), start /* offset */, 
	    				replacement_length+1, c.getName().length());
	    		ret.add(p);
	    	}
	    }
		

		return ret.toArray(new ICompletionProposal[ret.size()]);
	}

	
	public IContextInformation[] computeContextInformation(
			ITextViewer viewer, int offset) {
		return NO_CONTEXTS;
	}

	
	public char[] getCompletionProposalAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	
	public char[] getContextInformationAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
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

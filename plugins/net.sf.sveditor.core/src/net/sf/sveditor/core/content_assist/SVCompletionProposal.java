package net.sf.sveditor.core.content_assist;

import net.sf.sveditor.core.db.SVDBItem;

public class SVCompletionProposal {
	
	private SVDBItem				fItem;
	private String					fReplacement;
	private int						fStartOffset;
	private int						fReplacementLength;
	
	public SVCompletionProposal(SVDBItem item) {
		fItem = item;
	}
	
	public String getReplacement() {
		return fReplacement;
	}
	
	public SVCompletionProposal(
			String 				replacement, 
			int 				startOffset, 
			int 				replacementLength) {
		fReplacement 		= replacement;
		fStartOffset 		= startOffset;
		fReplacementLength 	= replacementLength;
	}
	
	public SVDBItem getItem() {
		return fItem;
	}

}

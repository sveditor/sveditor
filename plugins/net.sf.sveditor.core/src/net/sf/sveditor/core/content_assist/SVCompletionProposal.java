package net.sf.sveditor.core.content_assist;

import net.sf.sveditor.core.db.SVDBItem;

public class SVCompletionProposal {
	
	private SVDBItem				fItem;
	private String					fPrefix;
	private String					fReplacement;
	private int						fReplacementOffset;
	private int						fReplacementLength;
	
	public SVCompletionProposal(
			SVDBItem 		item,
			String			prefix,
			int				replacementOffset,
			int				replacementLength) {
		fItem 				= item;
		fPrefix 			= prefix;
		fReplacementOffset 	= replacementOffset;
		fReplacementLength 	= replacementLength;
	}
	
	public String getPrefix() {
		return fPrefix;
	}
	
	public String getReplacement() {
		return fReplacement;
	}
	
	public void setReplacement(String replacement) {
		fReplacement = replacement;
	}
	
	public SVCompletionProposal(
			String 				replacement, 
			int 				startOffset, 
			int 				replacementLength) {
		fReplacement 		= replacement;
		fReplacementOffset 	= startOffset;
		fReplacementLength 	= replacementLength;
	}
	
	public SVDBItem getItem() {
		return fItem;
	}
	
	public int getReplacementOffset() {
		return fReplacementOffset;
	}
	
	public int getReplacementLength() {
		return fReplacementLength;
	}

}

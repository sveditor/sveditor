package net.sf.sveditor.core.argfile.content_assist;

import net.sf.sveditor.core.db.ISVDBItemBase;

public class SVArgFileCompletionProposal {
	
	private String				fPrefix;
	private int				fReplacementOffset;
	private int				fReplacementLength;

	public SVArgFileCompletionProposal(
			String			prefix,
			int				replacementOffset,
			int				replacementLength) {
		fPrefix = prefix;
		fReplacementOffset = replacementOffset;
		fReplacementLength = replacementLength;
	}
}

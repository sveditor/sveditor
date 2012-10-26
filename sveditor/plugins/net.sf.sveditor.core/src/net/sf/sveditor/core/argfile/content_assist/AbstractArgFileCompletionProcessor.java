package net.sf.sveditor.core.argfile.content_assist;

import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class AbstractArgFileCompletionProcessor implements ILogLevel {
	
	public AbstractArgFileCompletionProcessor() {
		
	}
	
	public void computeProposals(
			IBIDITextScanner		scanner,
			int						lineno,
			int						linepos) {
		
	}
	
	protected void addProposal(SVArgFileCompletionProposal proposal) {
		
	}

}

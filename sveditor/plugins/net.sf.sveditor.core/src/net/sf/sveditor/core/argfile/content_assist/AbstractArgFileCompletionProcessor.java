package net.sf.sveditor.core.argfile.content_assist;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class AbstractArgFileCompletionProcessor implements ILogLevel {
	protected List<SVArgFileCompletionProposal>			fProposals;
	protected LogHandle									fLog;
	
	public AbstractArgFileCompletionProcessor(LogHandle log) {
		fProposals = new ArrayList<SVArgFileCompletionProposal>();
		fLog = log;
	}
	
	public void computeProposals(
			IBIDITextScanner		scanner,
			int						lineno,
			int						linepos) {
		
	}
	
	protected void addProposal(SVArgFileCompletionProposal proposal) {
		if (!fProposals.contains(proposal)) {
			fProposals.add(proposal);
		}
	}

}

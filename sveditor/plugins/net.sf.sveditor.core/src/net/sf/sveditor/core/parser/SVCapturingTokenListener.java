package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

public class SVCapturingTokenListener implements ISVTokenListener {
	private List<SVToken>				fTokenList;
	
	public SVCapturingTokenListener() {
		fTokenList = new ArrayList<SVToken>();
	}

	public List<SVToken> getTokenList() {
		return fTokenList;
	}

	public void tokenConsumed(SVToken tok) {
		fTokenList.add(tok);
	}

	public void ungetToken(SVToken tok) { 
		if (fTokenList.size() > 0) {
			fTokenList.remove(fTokenList.size()-1);
		}
	}

}

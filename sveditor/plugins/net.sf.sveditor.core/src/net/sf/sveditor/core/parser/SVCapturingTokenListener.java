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
		fTokenList.add(tok.duplicate());
	}

	public void ungetToken(SVToken tok) { 
		if (fTokenList.size() > 0) {
			fTokenList.remove(fTokenList.size()-1);
		}
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		for (int i=0; i<fTokenList.size(); i++) {
			sb.append(fTokenList.get(i).getImage());
			if (i+1 < fTokenList.size()) {
				sb.append(" ");
			}
		}
		
		return sb.toString();
	}

}

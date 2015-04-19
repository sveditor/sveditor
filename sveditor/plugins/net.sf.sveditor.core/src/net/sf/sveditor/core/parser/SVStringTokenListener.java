package net.sf.sveditor.core.parser;

public class SVStringTokenListener implements ISVTokenListener {
	private StringBuilder			fString = new StringBuilder();
	private int						fCount;
	private boolean					fSpaceTokens;
	
	@Override
	public void tokenConsumed(SVToken tok) {
		if (fSpaceTokens && fCount > 0) {
			fString.append(" ");
		}
		fString.append(tok.getImage());
		fCount++;
	}

	@Override
	public void ungetToken(SVToken tok) {
		if (fCount > 0) {
			if (fCount > 1) {
				if (fSpaceTokens) {
					fString.setLength(fString.length()-tok.getImage().length()-1);
				} else {
					fString.setLength(fString.length()-tok.getImage().length());
				}
			} else {
				fString.setLength(0);
			}
			fCount--;
		}
	}
	
	public String toString() {
		return fString.toString();
	}

}

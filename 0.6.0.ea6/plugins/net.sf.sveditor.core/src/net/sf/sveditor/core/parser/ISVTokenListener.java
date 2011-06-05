package net.sf.sveditor.core.parser;

public interface ISVTokenListener {
	
	void tokenConsumed(SVToken tok);
	
	void ungetToken(SVToken tok);

}

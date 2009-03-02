package net.sf.sveditor.core.scanner;

public interface ITextScanner {
	
	int get_ch();
	
	void unget_ch(int ch);
	
	int skipWhite(int ch);
	
	String readIdentifier(int ch);
	
	void startCapture(int ch);
	
	String endCapture();
	
	int skipPastMatch(String pair);
	
	String readString(int ch);

}

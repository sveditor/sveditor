package net.sf.sveditor.core.scanutils;

public interface ITextScanner {
	
	int get_ch();
	
	void unget_ch(int ch);
	
	int skipWhite(int ch);
	
	String readIdentifier(int ch);
	
	void startCapture(int ch);
	
	String endCapture();
	
	int skipPastMatch(String pair);
	
	String readString(int ch);
	
	ScanLocation getLocation();

}

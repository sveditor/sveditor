package net.sf.sveditor.core.scanutils;

public interface IRandomAccessTextScanner extends ITextScanner {
	
	long getPos();
	
	void seek(long pos);
	
	String get_str(long start, int length);

}

package net.sf.sveditor.core.parser2;


public class FileInfo {
	String				fName    = "";
	int					fLineno  = 1;
	int					fLinepos = 0;
	
	public FileInfo(String name) {
		fName = name; 
	}
}

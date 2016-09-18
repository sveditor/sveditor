package net.sf.sveditor.svutils;

import java.util.List;

public abstract class CommandBase {
	protected String			fName;
	protected boolean			fVerbose;
	protected boolean			fDebug;
	
	protected CommandBase(String name) {
		fName = name;
	}
	
	public abstract int run(List<Argument> args);
	
	protected void info(String msg) {
		
	}
	
	protected void error(String msg) {
		
	}
	
	protected void fatal(String msg) {
		System.out.println("Fatal: " + msg);
		
	}
	
	protected void verbose(String msg) {
		
	}
	
	protected void debug(String msg) {
		
	}

}

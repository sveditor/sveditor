package net.sf.sveditor.ui.script.launch;

public class ConsoleAction {
	private ConsoleActionType				fType;
	
	protected ConsoleAction(ConsoleActionType type) {
		fType = type;
	}
	
	public ConsoleActionType getType() {
		return fType;
	}

}

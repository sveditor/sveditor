package net.sf.sveditor.ui.script.launch;

import org.eclipse.ui.console.MessageConsoleStream;

public class AddTextConsoleAction extends ConsoleAction {
	
	private String					fText;
	private MessageConsoleStream	fStream;
	
	public AddTextConsoleAction(String text, MessageConsoleStream stream) {
		super(ConsoleActionType.AddText);
		fText = text;
		fStream = stream;
	}
	
	public String getText() {
		return fText;
	}
	
	public MessageConsoleStream getStream() {
		return fStream;
	}

}

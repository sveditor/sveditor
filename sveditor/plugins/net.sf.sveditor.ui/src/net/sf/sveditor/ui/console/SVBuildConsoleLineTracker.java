package net.sf.sveditor.ui.console;

import org.eclipse.debug.ui.console.IConsole;
import org.eclipse.debug.ui.console.IConsoleLineTracker;
import org.eclipse.jface.text.IRegion;

import net.sf.sveditor.ui.script.launch.GenericPathPatternMatcher;

public class SVBuildConsoleLineTracker implements IConsoleLineTracker {
	private GenericPathPatternMatcher		fPathMatcher;
	private SVProcessConsole				fConsole;

	@Override
	public void init(IConsole console) {
		
		if (console instanceof SVProcessConsole) {
			fConsole = (SVProcessConsole)console;
		
			fPathMatcher = new GenericPathPatternMatcher();
			console.addPatternMatchListener(fPathMatcher);
			console.addPatternMatchListener(new WorkspacePathPatternMatcher());
		}
	}

	@Override
	public void lineAppended(IRegion line) {
//		String msg = fConsole.getDocument().get(line.getOffset(), line.getLength());
//		fPathMatcher.
	}

	@Override
	public void dispose() { }

}

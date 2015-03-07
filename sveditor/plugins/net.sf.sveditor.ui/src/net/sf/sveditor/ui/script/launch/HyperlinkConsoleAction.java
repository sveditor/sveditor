package net.sf.sveditor.ui.script.launch;

import org.eclipse.core.resources.IFile;

public class HyperlinkConsoleAction extends ConsoleAction {
	private IFile					fPath;
	private int						fPos;
	private int						fLen;
	private int						fLineno = -1;
	
	public HyperlinkConsoleAction(IFile path, int pos, int len) {
		super(ConsoleActionType.Hyperlink);
		fPath = path;
		fPos = pos;
		fLen = len;
	}
	
	public void setLineno(int line) {
		fLineno = line;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public IFile getPath() {
		return fPath;
	}
	
	public int getPos() {
		return fPos;
	}
	
	public int getLen() {
		return fLen;
	}

}

package net.sf.sveditor.ui.script.launch;

import java.io.File;

import net.sf.sveditor.core.SVFileUtils;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.ui.console.FileLink;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.ui.console.IPatternMatchListener;
import org.eclipse.ui.console.PatternMatchEvent;
import org.eclipse.ui.console.TextConsole;

public class GenericPathPatternMatcher implements IPatternMatchListener {
	private TextConsole			fConsole;

	@Override
	public void connect(TextConsole console) {
		fConsole = console;
	}

	@Override
	public void disconnect() {
		// TODO Auto-generated method stub

	}
	
	@Override
	public void matchFound(PatternMatchEvent event) {
		String content = null;
		try {
			content = fConsole.getDocument().get(event.getOffset(), event.getLength());
		} catch (BadLocationException e) {}
		
		if (content == null) {
			return;
		}
		
		content = content.trim();
		
		int paren_idx=-1;
		int colon_idx=-1;
		int lineno=-1;
		int sp_idx=-1;
	
		if (SVFileUtils.isWin()) {
			content = content.replace('\\', '/');
			
			// Recognize MinGW-style paths: /c/foo/path
			// Convert to Windows-type path: c:/foo/path
			if (content.length() >= 3 && 
					(content.charAt(0) == '/') &&
					(content.charAt(2) == '/')) {
				int ch = Character.toLowerCase(content.charAt(1));
				
				if (ch >= 'a' && ch <= 'z') {
					content = content.charAt(1) + ":" + content.substring(2);
				}
			}
		}
		
		if ((paren_idx=content.indexOf('(')) != -1) {
			int end_idx=paren_idx+1;
			
			while (end_idx<content.length() && 
					Character.isDigit(content.charAt(end_idx))) {
				end_idx++;
			}
			
			String number = (end_idx<content.length())?
					content.substring(paren_idx+1,end_idx):
						content.substring(paren_idx+1);
					
			content = content.substring(0,paren_idx);
			
			try {
				lineno = Integer.parseInt(number);
			} catch (NumberFormatException e) {}
		} else if ((colon_idx=content.indexOf(':')) != -1) {
			if (colon_idx != 1 || (colon_idx=content.indexOf(':',colon_idx+1)) != -1) {
				int end_idx=colon_idx+1;

				while (end_idx<content.length() && 
						Character.isDigit(content.charAt(end_idx))) {
					end_idx++;
				}

				String number = (end_idx<content.length())?
						content.substring(colon_idx+1,end_idx):
							content.substring(colon_idx+1);

				content = content.substring(0,colon_idx);

				try {
					lineno = Integer.parseInt(number);
				} catch (NumberFormatException e) {}			
			}
		} else if ((sp_idx=content.indexOf(' ')) != -1) {
			// See if there's a trailing number.
			int idx = sp_idx;
			while (idx < content.length() && 
					Character.isWhitespace(content.charAt(idx))) {
				idx++;
			}
			
			if (idx < content.length() && 
					content.charAt(idx) >= '0' && content.charAt(idx) <= '9') {
				String number = content.substring(idx).trim();
				content = content.substring(0, sp_idx);
				try {
					lineno = Integer.parseInt(number);
				} catch (NumberFormatException e) {
					e.printStackTrace();
				}
			}
		}
	
		IFile file = SVFileUtils.findWorkspaceFile(content);
		File efile = SVFileUtils.getFile(content);
	
		// Eclipse sometimes returns a file (that doesn't exist) for
		// a directory path. We only want to hyperlink 'real' files.
		if (file != null && file.exists()) {
			FileLink link = new FileLink(file, null, -1, -1, lineno);
			try {
				fConsole.addHyperlink(link, event.getOffset(), content.length());
			} catch (BadLocationException e) {}
		} else if (efile != null && efile.isFile()) {
			IFileStore fs = EFS.getLocalFileSystem().getStore(new Path(efile.getAbsolutePath()));
			ExternalPathHyperlink link = new ExternalPathHyperlink(fs, null, -1, -1, lineno);
			try {
				fConsole.addHyperlink(link, event.getOffset(), content.length());
			} catch (BadLocationException e) {}
		}
	}

	@Override
	public String getPattern() {
		return "([a-zA-Z]:)?[/\\\\][^ \\t\\r\\n]+([ \\t]+[0-9]+)?";
	}

	@Override
	public int getCompilerFlags() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String getLineQualifier() {
		// TODO Auto-generated method stub
		return null;
	}

}

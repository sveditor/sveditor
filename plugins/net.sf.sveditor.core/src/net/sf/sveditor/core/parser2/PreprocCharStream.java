package net.sf.sveditor.core.parser2;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.scanner.EOFException;

public class PreprocCharStream implements CharStream {
	private Stack<InputStream>			fInputStack;
	private Stack<FileInfo>				fFileInfoStack;
	private int                         fLineno;
	private int							fLinepos;
	private int							fBeginLineno;
	private int							fBeginLinepos;
	private StringBuffer				fImage;
	private StringBuffer				fUngetBuf;
	private List<String>				fIncludePaths;
	private Stack<Boolean>				fEnStack;
	private Map<String, Macro>			fMacroMap;
	
	public PreprocCharStream(InputStream in, String path) {
		fInputStack = new Stack<InputStream>();
		fInputStack.push(in);
		fFileInfoStack = new Stack<FileInfo>();
		fFileInfoStack.push(new FileInfo(path));
		
		fEnStack = new Stack<Boolean>();
		fEnStack.push(true);
		
		fIncludePaths = new ArrayList<String>();
		
		fIncludePaths.add("c:/tools/ovm/ovm-2.0/src");
		fIncludePaths.add("c:/usr1/fun/sveditor");
		
		fMacroMap = new HashMap<String, Macro>();
		
		fLineno   = 1;
		fLinepos  = 0;
		fImage    = new StringBuffer();
		fUngetBuf = new StringBuffer();
	}

	public char BeginToken() throws IOException {
		fImage.setLength(0);
		
		char ret = get_ch();
		fImage.append(ret);

		fBeginLineno = getLineno();
		fBeginLinepos = getLinepos();
		
		return ret;
	}
	
	int getLineno() {
		return fFileInfoStack.peek().fLineno;
	}
	
	int getLinepos() {
		return fFileInfoStack.peek().fLinepos;
	}

	public void Done() {
		// TODO Auto-generated method stub
	}

	public String GetImage() {
		return fImage.toString();
	}

	public char[] GetSuffix(int len) {
		return fImage.substring(fImage.length() - len, fImage.length()).toCharArray();
	}

	public void backup(int amount) {
		if (amount > 0) {
			for (int i=amount; i>0; i--) {
				fUngetBuf.append(fImage.charAt(fImage.length()-i));
			}
			fImage.setLength(fImage.length()-amount);
		}
	}

	public int getBeginColumn() {
		return fBeginLinepos;
	}

	public int getBeginLine() {
		return fBeginLineno;
	}

	public int getColumn() {
		return fLinepos;
	}

	public int getEndColumn() {
		return fBeginLinepos + fImage.length();
	}

	public int getEndLine() {
		// TODO: this might not be correct
		return fBeginLineno;
	}

	public int getLine() {
		return getLineno();
	}

	public char readChar() throws IOException {
		char ret = get_ch();
		fImage.append(ret);
		
		return ret;
	}
	
	private char get_ch() throws IOException {
		int ch = -1;
		
		// Skip disabled code sections
		while ((ch = get_ch_preproc()) != -1 && !fEnStack.peek());
		
		return (char)ch;
	}
	
	private void unget_ch(int ch) {
		fUngetBuf.append((char)ch);
	}
	
	// Gets the next non-comment (and non-preproc) char
	private char get_ch_preproc() throws IOException {
		int ch = -1;
		
		while (true) {
			ch = get_ch_ll();
			
			if (ch == '/') {
				int ch2 = get_ch_ll();
				if (ch2 == '/') {
					// scan to end-of-line
					while ((ch = get_ch_ll()) != -1 && ch != '\n');
					break;
				} else if (ch2 == '*') {
					int ch_a[] = {-1, -1};
					
					// multi-line comment
					do {
						ch_a[0] = ch_a[1]; 
						
						if ((ch_a[1] = get_ch_ll()) == -1) {
							break;
						}
					} while (ch_a[0] != '*' || ch_a[1] != '/');
				} else {
					fUngetBuf.append(ch2);
					break;
				}
			} else if (ch == '`') {
				// TODO: pre-processor
				
				int lineno = fFileInfoStack.peek().fLineno;
				String file = fFileInfoStack.peek().fName;
				
//				int ch2 = get_ch_ll();
				
				// First check for one- or two-character pre-proc directives
				ch = get_ch_ll();
				ch = skipWhite(ch);
				
				String dir = readIdentifier(ch);
				
				if (dir.equals("include")) {
					StringBuffer sb = new StringBuffer();
					// now, look for file to include
					
					while ((ch = get_ch_ll()) != -1 && ch != '"');
					
					// Now, read the filename
					sb.setLength(0);
					while ((ch = get_ch_ll()) != -1 && ch != '"') {
						sb.append((char)ch);
					}
					System.out.println("include \"" + sb.toString() + "\"");
					InputStream inc_in = openIncludeFile(sb.toString());
					
					if (inc_in != null) {
						fInputStack.push(inc_in);
						fFileInfoStack.push(new FileInfo(sb.toString()));
					} else {
						System.out.println("[ERROR] cannot open included file \"" +
								sb.toString() + "\"");
					}
				} else if (dir.equals("define")) {
					int end_of_macro_idx = 0;
					
					ch = get_ch_ll();
					ch = skipWhite(ch);
					
					String remainder_line = readLine(ch);
					
					System.out.println("remainder_line=" + remainder_line);

					// complete parsing
					// skip forward to end-of-definition to determine 
					// whether this macro has arguments
					
					int i;
					for (i=0; i<remainder_line.length(); i++) {
						ch = remainder_line.charAt(i);
						
						if (!(
								(ch >= 'a' && ch <= 'z') ||
								(ch >= 'A' && ch <= 'Z') ||
								(ch >= '0' && ch <= '9') ||
								ch == '_')) {
							break;
						}
					}
					
					Macro m  = new Macro();
					m.fName = remainder_line.substring(0, i);
					
					if (ch == '(') {
						// macro with arguments
						/*
						System.out.println("[TODO] macro with arguments: " +
								m.fName + "=" +
								remainder_line.substring(i));
						 */
						m.fValue = "";
					} else {
						// no-argument macro
						
						// Skip any whitespace
						for (; (i<remainder_line.length() && 
								Character.isWhitespace(remainder_line.charAt(i))); i++);
						
						m.fValue = remainder_line.substring(i); 
					}
					
					fMacroMap.put(remainder_line, m);
				} else if (dir.startsWith("if")) {
					// read the next token
					ch = get_ch_ll();
					ch = skipWhite(ch);
					String cond = readIdentifier(ch);
					
					System.out.println("cond=" + cond);
					
					
					if (dir.equals("ifdef")) {
						fEnStack.push(fMacroMap.containsKey(cond));
					} else if (dir.equals("ifndef")) {
						fEnStack.push(!fMacroMap.containsKey(cond));
					}
				} else if (dir.equals("endif")) {
					fEnStack.pop();
				} else if (dir.equals("else")) {
					boolean val = fEnStack.pop();
					fEnStack.push(!val);
				} else {
					System.out.println("unrecognized macro: \"" + dir + "\" @ " +
							file + ":" + lineno);
					// probably
				}

				// break;
			} else {
				// Not a comment-begin
				break;
			}
		}
		
		return (char)ch;
	}
	
	private InputStream openIncludeFile(String file) {
		InputStream ret = null;
		
		for (String path : fIncludePaths) {
			File f = new File(path, file);
			
			if (f.isFile()) {
				try {
					ret = new FileInputStream(f);
					break;
				} catch (IOException e) {
				}
			}
		}
		
		return ret;
	}
	
	private char get_ch_ll() throws IOException {
		int ret = -1;
		if (fUngetBuf.length() > 0) {
			ret = fUngetBuf.charAt(fUngetBuf.length()-1);
			fUngetBuf.setLength(fUngetBuf.length()-1);
		} else {
			while (ret == -1 && fInputStack.size() > 0) {
				InputStream in   = fInputStack.peek();
				try {
					ret = in.read();
				} catch (IOException e) {
				}
				if (ret == -1 && fInputStack.size() > 0) {
					fInputStack.pop();
					fFileInfoStack.pop();
				}
			}
			
			if (ret == -1) {
				throw new IOException("EOF");
			}
		}

		// Only change input position if in top-level
		if (fFileInfoStack.size() > 0) {
			FileInfo    info = fFileInfoStack.peek();
			
			if (ret == '\n') {
				info.fLineno++;
				info.fLinepos = 0;
			}
			info.fLinepos++;
		}
		
		if (fInputStack.size() == 1) {
			if (ret == '\n') {
				fLineno++;
				fLinepos = 0;
			}
			fLinepos++;
		}
		
		return (char)ret;
	}
	
	public int skipWhite(int ch) throws IOException {

		// Skip whitespace. Consider the line-continuation character as WS
		while (Character.isWhitespace(ch) || ch == '\\') {
			int tmp = get_ch_ll();
			
			if (ch == '\\' && (tmp != '\r' && tmp != '\n')) {
				unget_ch(tmp);
				return ch;
			}
			ch = tmp;
		}
		
		return ch;
	}

	private String readIdentifier(int ci) throws IOException {
		StringBuffer buf = null;
		
		try {
			if (!Character.isJavaIdentifierStart(ci)) {
				unget_ch(ci);
				return null;
			}
		
			buf = new StringBuffer();
			buf.append((char)ci);
		
			while ((ci = get_ch_ll()) != -1 && Character.isJavaIdentifierPart(ci)) {
				buf.append((char)ci);
			}
			unget_ch(ci);
		} catch (IOException e) {
			if (buf == null || buf.length() == 0) {
				throw e;
			}
		}
		
		return buf.toString();
	}

	private String readLine(int ci) throws IOException {
		int last_ch = -1;
		StringBuffer ret = new StringBuffer();

		try {
			while (ci != '\n' || last_ch == '\\') {
				if (last_ch == '\\' && ci == '\n') {
					if (ret.charAt(ret.length()-1) == '\r') {
						ret.setLength(ret.length()-1);
					}
					if (ret.charAt(ret.length()-1) == '\\') {
						ret.setCharAt(ret.length()-1, '\n');
					}
				} else {
					ret.append((char)ci);
				}

				if (ci != '\r') {
					last_ch = ci;
				}

				ci = get_ch_ll();
			}
		} catch (IOException e) {
			if (ret.length() == 0) {
				throw e;
			}
		}
		
		return ret.toString();
	}


	private class Macro {
		String						fName;
		List<String>				fArguments = new ArrayList<String>();
		String						fValue;
		
	}
}

/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.argfile.parser;

import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ISVParser;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.scanutils.ITextScanner;

public class SVArgFileLexer extends SVArgFileToken {
	private ITextScanner 				fScanner;
	// 2- and 3-character operator prefixes

//	private List<ISVArgFileTokenListener> fTokenListeners;

	private boolean 					fTokenConsumed;

	private StringBuilder 				fStringBuffer;
	private static final boolean		fDebugEn = false;
	private boolean 					fEOF;

	private StringBuilder				fCaptureBuffer;
	private boolean 					fCapture;
	private SVArgFileToken 				fCaptureLastToken;
	private ISVParser 					fParser;
	private Stack<SVArgFileToken>		fUngetStack;
	private LogHandle					fLog;

	public SVArgFileLexer() {
		fLog = LogFactory.getLogHandle("SVArgFileLexer");

		fStringBuffer = new StringBuilder();
		fCaptureBuffer = new StringBuilder();
		fCapture = false;

		fUngetStack = new Stack<SVArgFileToken>();

//		fTokenListeners = new ArrayList<ISVArgFileTokenListener>();

		fEOF = false;
	}

	/*
	public void addTokenListener(ISVArgFileTokenListener l) {
		fTokenListeners.add(l);
	}

	public void removeTokenListener(ISVArgFileTokenListener l) {
		fTokenListeners.remove(l);
	}
	 */
	
	public void init(ISVParser parser, ITextScanner scanner) {
		fTokenConsumed = true;
		fScanner = scanner;
		fEOF = false;
		fParser = parser;
	}

	public void init(SVArgFileToken tok) {
		fImage = tok.getImage();
		fIsPath = tok.isPath();
		fIsOption = tok.isOption();
		fStartLocation = tok.getStartLocation();
	}

	public SVArgFileToken peekToken() {
		peek();

		return this.duplicate();
	}

	// Returns a token
	public SVArgFileToken consumeToken() {
		if (peek() != null) {;
			SVArgFileToken tok = this.duplicate();
			eatToken();

			return tok;
		} else {
			return null;
		}
	}
	
	public String readPath() throws SVParseException {
		peek();
		
		if (!fIsPath) {
			error("Expecting a path argument. Received \"" + fImage + "\"");
		}
		
		return eatToken();
	}
	
	public String readOption(String ... opts) throws SVParseException {
		peek();

		boolean found = false;
		
		if (fIsOption) {
			if (opts.length == 0) {
				found = true;
			} else if (opts.length == 1) {
				found = fImage.equals(opts[0]);
			} else if (opts.length == 2) {
				found = (fImage.equals(opts[0]) || fImage.equals(opts[1]));
			} else {
				for (String opt : opts) {
					if (fImage.equals(opt)) {
						found = true;
						break;
					}
				}
			}
		}
		
		if (!found) {
			StringBuilder sb = new StringBuilder();
			
			for (int i=0; i<opts.length; i++) {
				sb.append(opts[i]);
				if (i+1 < opts.length) {
					sb.append(", ");
				}
			}
			
			error("Expecting one of options \"" + sb.toString() + "\" ; " +
					"received \"" + fImage + "\"");
		}
		
		return eatToken();
	}

	public void ungetToken(SVArgFileToken tok) {
		if (fDebugEn) {
			debug("ungetToken : \"" + tok.getImage() + "\"");
		}
		// If the current token is valid, then push it back
		if (!fTokenConsumed) {
			fUngetStack.push(this.duplicate());
		}
		fTokenConsumed = true; // ensure we move to the next

		if (fCapture) {
			if (fCaptureBuffer.length() >= tok.getImage().length()) {
				fCaptureBuffer.setLength(fCaptureBuffer.length()
						- tok.getImage().length());
			}
			// Remove separator
			if (fCaptureBuffer.length() > 0
					&& fCaptureBuffer.charAt(fCaptureBuffer.length() - 1) == ' ') {
				fCaptureBuffer.setLength(fCaptureBuffer.length() - 1);
			}
			fCaptureLastToken = tok.duplicate();
		}

		/*
		if (fTokenListeners.size() > 0) {
			for (ISVArgFileTokenListener l : fTokenListeners) {
				l.ungetToken(tok);
			}
		}
		 */

		fUngetStack.push(tok);
		peek();
		if (fDebugEn) {
			debug("After un-get of token \"" + tok.getImage()
					+ "\" next token is \"" + peek() + "\"");
		}
	}

	public void ungetToken(List<SVArgFileToken> tok_l) {
		for (int i = tok_l.size() - 1; i >= 0; i--) {
			ungetToken(tok_l.get(i));
		}
	}

	public String peek() {
		if (fTokenConsumed) {
			if (fEOF || !next_token()) {
				fImage = null;
			}
			if (fDebugEn) {
				debug("peek() -- \"" + fImage + "\" " + fEOF);
			}
		}
		return fImage;
	}
	
	public boolean peekOption(String ... options) {
		if (options.length == 0 && fIsOption) {
			return true;
		} else if (fIsOption) {
			for (String opt : options) {
				if (fImage.equals(opt)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public String eatToken() {
		peek();
		if (fCapture) {
			if (fCaptureBuffer.length() > 0) {
				fCaptureBuffer.append(" ");
			}
			fCaptureBuffer.append(fImage);
			fCaptureLastToken = duplicate(); // copy token
		}
		/*
		if (fTokenListeners.size() > 0) {
			SVArgFileToken tok = this.duplicate();
			for (ISVArgFileTokenListener l : fTokenListeners) {
				l.tokenConsumed(tok);
			}
		}
		 */
		fTokenConsumed = true;
		return fImage;
	}

	private boolean next_token() {
		if (fEOF && fUngetStack.size() == 0) {
			/*
			 * if (fEnableEOFException) { throw new EOFException(); } else {
			 * return false; }
			 */
			return false;
		}
		try {
			if (fUngetStack.size() > 0) {
				if (fDebugEn) {
					debug("next_token: unget_stack top="
							+ fUngetStack.peek().getImage());
				}
				init(fUngetStack.pop());
				fTokenConsumed = false;
				return true;
			} else {
				return next_token_int();
			}
		} catch (SVParseException e) {
			return false;
		}
	}

	public void skipPastMatch(String start, String end, String... escape) {
		int start_c = 1, end_c = 0;

		if (peek().equals(start)) {
			eatToken();
		}

		while (peek() != null && start_c != end_c) {
			if (peek().equals(start)) {
				start_c++;
			} else if (peek().equals(end)) {
				end_c++;
			} else if (escape.length > 0) {
				for (String e : escape) {
					if (peek().equals(e)) {
						return;
					}
				}
			}
			eatToken();
		}
	}

	public void startCapture() {
		fCaptureBuffer.setLength(0);
		fCapture = true;
	}

	public String endCapture() {
		fCapture = false;
		fCaptureLastToken = null;

		return fCaptureBuffer.toString();
	}

	private boolean next_token_int() throws SVParseException {
		int ch = fScanner.get_ch();
		int ch2 = -1;
		boolean is_string = false;
		
		if (fDebugEn) {
			fLog.debug("--> next_token_int()");
		}

		fIsOption = false;
		fIsPath = false;
		fOptionVal = null;
		fOptionOp = null;

		while (true) {
			if (ch == '/') {
				ch2 = fScanner.get_ch();

				if (ch2 == '/') {
					while ((ch = fScanner.get_ch()) != -1 && ch != '\n') {
					}
				} else if (ch2 == '*') {
					int cc_1 = -1, cc_2 = -1;

					while ((ch = fScanner.get_ch()) != -1) {
						cc_1 = cc_2;
						cc_2 = ch;

						if (cc_1 == '*' && cc_2 == '/') {
							break;
						}
					}

					ch = ' ';
				} else {
					fScanner.unget_ch(ch2);
					break;
				}
			} else {
				if (!Character.isWhitespace(ch)) {
					break;
				}
			}
			ch = fScanner.get_ch();
		}

		fStringBuffer.setLength(0);

		// TODO: should fix
		fStartLocation = SVDBLocation.pack(
				fScanner.getFileId(),
				fScanner.getLineno(),
				fScanner.getLinepos());

		if (ch == -1) {
			fEOF = true;
		} else if (ch == '+' || ch == '-') {
			readOptionName(fStringBuffer, ch);
			
			ch = fScanner.get_ch();

			if (ch == '=' || !Character.isWhitespace(ch)) {
				StringBuilder sb = new StringBuilder();
				if (ch == '=') {
					fOptionOp = "=";
				} else {
					fOptionOp = "";
				}
				
				// Read follow-on option
				readStringOrPath(sb, ch);
				fOptionVal = sb.toString();
			} else {
				fScanner.unget_ch(ch);
			}
			fIsOption = true;
		} else {
			is_string = readStringOrPath(fStringBuffer, ch);
			fIsPath = true;
		} 

		if (fStringBuffer.length() == 0 && !is_string) {
			fEOF = true;
			
			if (fDebugEn) {
				debug("EOF - " + SVDBLocation.toString(getStartLocation()));
			}
			
			if (fDebugEn) {
				fLog.debug("<-- next_token_int()");
			}
			return false;
		} else {
			fImage = fStringBuffer.toString();

			fTokenConsumed = false;
			if (fDebugEn) {
				debug("next_token(): \"" + fImage + "\" @ " + 
						SVDBLocation.unpackLineno(getStartLocation()));
			}
			if (fDebugEn) {
				fLog.debug("<-- next_token_int()");
			}
			return true;
		}
	}
	
	private void readOptionName(StringBuilder sb, int ch) {
		int first_ch = ch;
	
		sb.append((char)first_ch);

		// Read until we reach whitespace
		while ((ch = fScanner.get_ch()) != -1) {
			if (Character.isWhitespace(ch) ||
					(first_ch == '+' && ch == '+') ||
					(ch == '=')) {
				break;
			}
			sb.append((char)ch);
		}
		
		if (first_ch == '+' && ch == '+') {
			sb.append((char)ch);
		} else {
			fScanner.unget_ch(ch);
		}
	}
	
	private boolean readStringOrPath(StringBuilder sb, int ch) {
		boolean is_string = false;

		if (ch == '"') {
			int last_ch = -1;
			// String
			sb.setLength(0);
			while ((ch = fScanner.get_ch()) != -1) {
				if (ch == '"' && last_ch != '\\') {
					break;
				}
				sb.append((char)ch);
				if (last_ch == '\\' && ch == '\\') {
					// Don't count a double quote
					last_ch = -1;
				} else {
					last_ch = ch;
				}
			}

			/*
			if (ch != '"') {
				error("Unterminated string");
			}
			 */
			is_string = true;
		} else {
			// Read a path -- everything up to EOL or whitespace
			sb.append((char)ch);
			while ((ch = fScanner.get_ch()) != -1 && !Character.isWhitespace(ch)) {
				sb.append((char)ch);
			}
			fScanner.unget_ch(ch);	
		}
		
		return is_string;
	}
	
	@SuppressWarnings("unused")
	private void append_ch(int ch) {
		fStringBuffer.append((char)ch);
		if (fDebugEn) {
			debug("append_ch: " + (char)ch + " => " + fStringBuffer.toString());
			if (ch == -1 || ch == 0xFFFF) {
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
	}

	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}

	private void error(String msg) throws SVParseException {
		endCapture();
		if (fParser != null) {
			fParser.error(msg);
		}
	}
}

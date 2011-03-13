/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVLexer extends SVToken {
	private ITextScanner				fScanner;
	private Set<String>					f2SeqPrefixes;
	private Set<String>					f3SeqPrefixes;
	private Set<String>					fOperatorSet;
	private Set<String>					fKeywordSet;
	
	private boolean						fTokenConsumed;
	private boolean						fNewlineAsOperator;
	
	private StringBuilder				fStringBuffer;
	private boolean						fDebugEn = false;
	private boolean						fEOF;
	
	private StringBuilder				fCaptureBuffer;
	private boolean						fCapture;
	private SVToken						fCaptureLastToken;
	private ISVParser					fParser;
	private Stack<SVToken>				fUngetStack;
		
	public static final String RelationalOps[] = {
		"&", "&&", "|", "||", 
		"-", "--", "+", "++",
		"%", "!", "*", "**", "/", 
		"^", "^~", "~^", "~", "?", 
		"<", "<<", "<=", "<<<",
		">", ">>", ">=", ">>>",
		"=", "*=", "/=", "%=", "+=", "==", "!=",
		"-=", "<<=", ">>=", "<<<=", ">>>=", "&=", "^=", "|=",
		"===", "!==", "==?", "!=?",
	};
	
	public static final String GroupingOps[] = {
		"(", ")", "{", "}", "[", "]",
	};
	
	public static final String MiscOps[] = {
		":", "::", ":/", ":=",
		"+:", "-:", // array-index operators
		",", ";", ".", ".*", "'",
		"->", "#", "##", "@", "@@"
	};
	
	private static final String AllOperators[];
	
	static {
		AllOperators = new String[RelationalOps.length + GroupingOps.length + MiscOps.length];
		int idx = 0;
		
		for (String o : RelationalOps) {
			AllOperators[idx++] = o;
		}
		
		for (String o : GroupingOps) {
			AllOperators[idx++] = o;
		}
		
		for (String o : MiscOps) {
			AllOperators[idx++] = o;
		}
	}
	
	public SVLexer() {
		f2SeqPrefixes = new HashSet<String>();
		f3SeqPrefixes = new HashSet<String>();
		fOperatorSet  = new HashSet<String>();
		
		fKeywordSet = new HashSet<String>();

		fStringBuffer = new StringBuilder();
		fCaptureBuffer = new StringBuilder();
		fCapture = false;
		
		fUngetStack = new Stack<SVToken>();
		
		for (String op : AllOperators) {
			if (op.length() == 3) {
				f3SeqPrefixes.add(op.substring(0, 1));
				f3SeqPrefixes.add(op.substring(0, 2));
			} else if (op.length() == 2) {
				f2SeqPrefixes.add(op.substring(0, 1));
			}
			fOperatorSet.add(op);
		}
		
		for (String kw : SVKeywords.getKeywords()) {
			if (kw.endsWith("*")) {
				kw = kw.substring(0,kw.length()-1);
			}
			fKeywordSet.add(kw);
		}
		fEOF = false;
	}
	
	public void setNewlineAsOperator(boolean en) {
		fNewlineAsOperator = en;
	}
	
	public void init(ISVParser parser, ITextScanner scanner) {
		fTokenConsumed 	= true;
		fScanner 		= scanner;
		fEOF 			= false;
		fParser 		= parser;
	}
	
	public void init(SVToken tok) {
		fImage = tok.fImage;
		fIsIdentifier = tok.fIsIdentifier;
		fIsKeyword = tok.fIsKeyword;
		fIsNumber = tok.fIsNumber;
		fIsOperator = tok.fIsOperator;
		fIsString = tok.fIsString;
		fIsTime = tok.fIsTime;
		fStartLocation = tok.fStartLocation.duplicate();
	}
	
	public SVToken peekToken() {
		peek();
		
		return this.duplicate();
	}
	
	// Returns a token 
	public SVToken consumeToken() {
		peek();
		SVToken tok = this.duplicate();
		eatToken();
		
		return tok;
	}
	
	public void ungetToken(SVToken tok) {
		// If the current token is valid, then push it back
		if (!fTokenConsumed) {
			fUngetStack.push(this.duplicate());
		}
		fTokenConsumed = true; // ensure we move to the next
		
		if (fCapture) {
			if (fCaptureBuffer.length() >= tok.getImage().length()) {
				fCaptureBuffer.setLength(fCaptureBuffer.length() - tok.getImage().length());
			}
			// Remove separator
			if (fCaptureBuffer.length() > 0 && fCaptureBuffer.charAt(fCaptureBuffer.length()-1) == ' ') {
				fCaptureBuffer.setLength(fCaptureBuffer.length()-1);
			}
			fCaptureLastToken = tok.duplicate();
		}
		
		fUngetStack.push(tok);
		peek();
		debug("After un-get of token \"" + tok.getImage() + "\" next token is \"" + peek() + "\"");
	}
	
	public void ungetToken(List<SVToken> tok_l) {
		for (int i=tok_l.size()-1; i>=0; i--) {
			ungetToken(tok_l.get(i));
		}
	}
	
	public String peek() {
		if (fTokenConsumed) {
			if (fEOF || !next_token()) {
				fImage = null;
			}
			debug("peek() -- \"" + fImage + "\" " + fEOF);
		}
		return fImage;
	}
	
	public boolean isIdentifier() {
		peek();
		return fIsIdentifier;
	}
	
	public boolean isNumber() {
		peek();
		return fIsNumber;
	}
	
	public boolean isTime() {
		peek();
		return fIsTime;
	}
	
	public boolean isKeyword() {
		peek();
		return fIsKeyword;
	}
	
	public boolean isOperator() {
		peek();
		return fIsOperator;
	}
	
	public boolean peekOperator(String ... ops) throws SVParseException {
		peek();
		
		if (fIsOperator) {
			if (ops.length == 0) {
				return true;
			} else {
				for (String op : ops) {
					if (fImage.equals(op)) {
						return true;
					}
				}
			}
		}
		return false;
	}

	public boolean peekOperator(Set<String> ops) throws SVParseException {
		peek();
		
		if (fIsOperator) {
			return ops.contains(fImage);
		}
		return false;
	}

	public boolean peekId() throws SVParseException {
		peek();
		
		return fIsIdentifier;
	}

	public boolean peekNumber() throws SVParseException {
		peek();
		
		return fIsNumber;
	}
	
	public String read() throws SVParseException {
		peek();
		
		return eatToken();
	}
	
	public String readOperator(String ... ops) throws SVParseException {
		peek();
		
		boolean found = false;
		if (fIsOperator) {
			if (ops.length == 0) {
				found = true;
			} else if (ops.length == 1) {
				found = fImage.equals(ops[0]);
			} else if (ops.length == 2) {
				found = fImage.equals(ops[0]) || fImage.equals(ops[1]);
			} else {
				for (String op : ops) {
					if (fImage.equals(op)) {
						found = true;
						break;
					}
				}
			}
		}
		
		if (!found) {
			StringBuilder sb = new StringBuilder();
			
			for (int i=0; i<ops.length; i++) {
				sb.append(ops[i]);
				if (i+1 < ops.length) {
					sb.append(", ");
				}
			}
			
			error("Expecting one of operator \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		return eatToken();
	}

	public boolean peekKeyword(String ... kw) throws SVParseException {
		peek();
		
		boolean found = false;
		if (kw.length == 1 && kw[0].equals("return") && fImage.equals("return")) {
			debug("RETURN: " + fIsKeyword);
		}
		if (fIsKeyword) {
			if (kw.length == 0) {
				found = true;
			} else if (kw.length == 1) {
				found = fImage.equals(kw[0]);
			} else if (kw.length == 2) {
				found = fImage.equals(kw[0]) || fImage.equals(kw[1]);
			} else if (kw.length == 3) {
				found = fImage.equals(kw[0]) || fImage.equals(kw[1]) || fImage.equals(kw[2]);
			} else if (kw.length == 4) {
				found = fImage.equals(kw[0]) || fImage.equals(kw[1]) || fImage.equals(kw[2]) || fImage.equals(kw[3]);
			} else {
				for (String k : kw) {
					if (fImage.equals(k)) {
						found = true;
						break;
					}
				}
			}
		}

		return found;
	}

	public boolean peekKeyword(Set<String> kw) throws SVParseException {
		peek();
		
		boolean found = false;
		if (fIsKeyword) {
			found = kw.contains(fImage);
		}

		return found;
	}

	public String readKeyword(Set<String> kw) throws SVParseException {
		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();
			
			for (String k : kw) {
				sb.append(k);
			}
			if (sb.length() > 2) {
				sb.setLength(sb.length()-2);
			}
			
			error("Expecting one of keyword \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		return eatToken();
	}
	
	public String readKeyword(String ... kw) throws SVParseException {
		
		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();
			
			for (int i=0; i<kw.length; i++) {
				sb.append(kw[i]);
				if (i+1 < kw.length) {
					sb.append(", ");
				}
			}
			
			error("Expecting one of keyword \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		return eatToken();
	}
	
	public String eatToken() {
		peek();
		if (fCapture) {
			if (fCaptureBuffer.length() > 0 && 
					((isIdentifier() && fCaptureLastToken.isIdentifier()) ||
					 (isNumber() && fCaptureLastToken.isNumber()))) {
				fCaptureBuffer.append(" ");
			}
			fCaptureBuffer.append(fImage);
			fCaptureLastToken = duplicate(); // copy token
		}
		fTokenConsumed = true;
		return fImage;
	}
	
	public String readString() throws SVParseException {
		peek();
		
		if (!fIsString) {
			error("Expecting a string ; received \"" + fImage + "\"");
		}
		
		return eatToken();
	}

	public boolean peekString() throws SVParseException {
		peek();
		
		return fIsString;
	}

	public String readId() throws SVParseException {
		peek();

		if (!fIsIdentifier) {
			error("Expecting an identifier ; received \"" + fImage + "\"");
		}
		
		return eatToken();
	}
	
	public SVToken readIdTok() throws SVParseException {
		peek();
		
		if (!fIsIdentifier) {
			error("Expecting an identifier ; received \"" + fImage + "\"");
		}
		
		return consumeToken();
	}
	
	public String readIdOrKeyword() throws SVParseException {
		peek();

		if (!fIsIdentifier && !fIsKeyword) {
			error("Expecting an identifier or keyword ; received \"" + 
					fImage + "\"");
		}
		
		return eatToken();
	}

	public String readNumber() throws SVParseException {
		peek();

		if (!fIsNumber) {
			error("Expecting a number ; received \"" + 
					fImage + "\"");
		}

		return eatToken();
	}
	
	private boolean next_token() {
		if (fEOF && fUngetStack.size() == 0) {
			/*
			if (fEnableEOFException) {
				throw new EOFException();
			} else {
				return false;
			}
			 */
			return false;
		}
		try {
			if (fUngetStack.size() > 0) {
				debug("next_token: unget_stack top=" + fUngetStack.peek().getImage());
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
	
	
	public void skipPastMatch(String start, String end, String ... escape) {
		int start_c=1, end_c=0;
		
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
		fCapture          = false;
		fCaptureLastToken = null;
		
		return fCaptureBuffer.toString();
	}
	
	private boolean next_token_int() throws SVParseException {
		int ch = get_ch();
		int ch2 = -1;
		
		fIsOperator    = false;
		fIsNumber      = false;
		fIsTime        = false;
		fIsIdentifier  = false;
		fIsKeyword     = false;
		fIsString      = false;
		
		// Skip whitespace and comments
		while (true) {
			if (ch == '/') {
				ch2 = get_ch();

				if (ch2 == '/') {
					while ((ch = get_ch()) != -1 && ch != '\n') {}
				} else if (ch2 == '*') {
					int end_comment[] = {-1, -1};

					while ((ch = get_ch()) != -1) {
						end_comment[0] = end_comment[1];
						end_comment[1] = ch;

						if (end_comment[0] == '*' && end_comment[1] == '/') {
							break;
						}
					}

					ch = ' ';
				} else {
					unget_ch(ch2);
					break;
				}
			} else {
				if (!Character.isWhitespace(ch) ||
						(ch == '\n' && fNewlineAsOperator)) {
					break;
				}
			}
			ch = get_ch();
		}
		fStringBuffer.setLength(0);
		String tmp = "" + (char)ch;
		
		// TODO: should fix
		ScanLocation loc = fScanner.getLocation();
		fStartLocation = new SVDBLocation(loc.getLineNo(), loc.getLinePos());

		if (ch == -1) {
			fEOF = true;
			/*
			if (fEnableEOFException) {
				throw new EOFException();
			}
			 */
		} else if (fNewlineAsOperator && ch == '\n') {
			fStringBuffer.append('\n');
			fIsOperator = true;
		} else if (ch == '"') {
			int last_ch = -1;
			// String
			while ((ch = get_ch()) != -1) {
				if (ch == '"' && last_ch != '\\') {
					break;
				}
				fStringBuffer.append((char)ch);
				last_ch = ch;
			}
			
			if (ch != '"') {
				error("Unterminated string");
			}
			fIsString = true;
		} else if (ch == '\'' || (ch >= '0' && ch <= '9')) {
			if (readNumber(ch)) {
				fIsNumber = true;
			} else {
				fIsOperator = true;
			}
			
			fImage = fStringBuffer.toString();

		} else if (fOperatorSet.contains(tmp) || 
				// Operators that can have up to two elements
				f2SeqPrefixes.contains(tmp) ||
				f3SeqPrefixes.contains(tmp)) {
			// Probably an operator in some form
			if (f2SeqPrefixes.contains(tmp)) {
				// Peek forward to see if the 2-wise sequence is present
				if ((ch2 = get_ch()) != -1) {
					String tmp2 = tmp + (char)ch2;
					if (fOperatorSet.contains(tmp2)) {
						if ((ch2 = get_ch()) != -1) {
							String tmp3 = tmp2 + (char)ch2;
							if (fOperatorSet.contains(tmp3)) {
								fStringBuffer.append(tmp3);
								fIsOperator = true;
							} else {
								unget_ch(ch2);
								fStringBuffer.append(tmp2);
								fIsOperator = true;
							}
						}
					} else {
						unget_ch(ch2);
						tmp = "" + (char)ch;
						if (fOperatorSet.contains(tmp)) {
							fStringBuffer.append(tmp);
							fIsOperator = true;
						}
					}
				} else {
					if (fOperatorSet.contains(tmp)) {
						fStringBuffer.append(tmp);
						fIsOperator = true;
					}
				}
			} else if (fOperatorSet.contains(tmp)) {
				// single-char operator
				fIsOperator = true;
				fStringBuffer.append(tmp);
			}
		
			if (!fIsOperator) {
				error("Bad partial operator: " + tmp);
			}
			
		} else if (SVCharacter.isSVIdentifierStart(ch)) {
			// Identifier or keyword
			fStringBuffer.append((char)ch);
			while ((ch = get_ch()) != -1 && SVCharacter.isSVIdentifierPart(ch)) {
				fStringBuffer.append((char)ch);
			}
			unget_ch(ch);
			// Handle case where we received a single '$'
			if (fStringBuffer.length() == 1 && fStringBuffer.charAt(0) == '$') {
				fIsOperator = true;
			} else {
				fIsIdentifier = true;
			}
		}
		
		if (fStringBuffer.length() == 0 && !fIsString) {
			fEOF = true;
			/*
			if (fEnableEOFException) {
				throw new EOFException();
			}
			 */
			debug("EOF");
			return false;
		} else {
		
			fImage = fStringBuffer.toString();

			if (fIsIdentifier) {
				if ((fIsKeyword = fKeywordSet.contains(fImage))) {
					if (SVKeywords.isSVKeyword(fImage)) {
						fIsIdentifier = false;
					}
				}
			}
			fTokenConsumed = false;
			debug("next_token(): \"" + fImage + "\"");
			return true;
		}
	}
	
	private boolean readNumber(int ch) throws SVParseException {
		boolean ret = true;
		if (ch == '\'') {
			fStringBuffer.append((char)ch);
			
			if ((ch = get_ch()) == -1) {
				error("unexpected EOF after \"'\"");
			}

			if (isBaseDigit(ch)) {
				// Append the base
				fStringBuffer.append((char)ch);
				
				// TODO: probably should be more selective here
				ch = readHexNumber(get_ch());
			} else {
				ret = false;
			}
		} else if (isHexDigit(ch)) {
			// Possibly a base...
			fStringBuffer.append((char)ch);

			ch = readDecNumber(get_ch());
			
			if (ch == '\'') {
				fStringBuffer.append((char)ch);
				
				// read the format character
				fStringBuffer.append((char)get_ch());
				
				// read balance of the number
				ch = readHexNumber(get_ch());
			} else {
				// Not a based number
				ch = readHexNumber(ch);
				
				// Probably a time
				if (ch == 'f' || ch == 'p' || ch == 'n' || ch == 'u' || ch == 'm') {
					fStringBuffer.append((char)ch);
					ch = get_ch();
					
					if (ch == 's') {
						fStringBuffer.append((char)ch);
						ch = -1;
					} else {
						error("[ERROR] unknown base " + (char)ch);
					}
					fIsTime = true;
					ch = -1;
				} else if (ch == 's') {
					fStringBuffer.append((char)ch);
					fIsTime = true;
					ch = -1;
				}
			}
		} else {
			ret = false;
		}
		
		if (ch != -1) {
			unget_ch(ch);
		}
		
		return ret;
	}
	
	private static boolean isHexDigit(int ch) {
		return ((ch >= '0' && ch <= '9') ||
				(ch >= 'a' && ch <= 'f') ||
				(ch >= 'A' && ch <= 'F') ||
				(ch == 'z' || ch == 'Z') ||
				(ch == 'x' || ch == 'X'));
	}
	
	private static boolean isBaseDigit(int ch) {
		return (ch == 'b' || ch == 'B' || ch == 'd' || ch == 'D' ||
				ch == 'h' || ch == 'H');
	}
	
	private int readDecNumber(int ch) throws SVParseException {
		while (ch >= '0' && ch <= '9') {
			fStringBuffer.append((char)ch);
			ch = get_ch();
		}
		return ch;
	}
	
	private int readHexNumber(int ch) throws SVParseException {
		while (ch != -1 && 
				((ch >= '0' && ch <= '9') ||
				 (ch >= 'a' && ch <= 'f') ||
				 (ch >= 'A' && ch <= 'F') ||
				 (ch == '_') || 
				 (ch == 'x') || (ch == 'X') ||
				 (ch == 'z') || (ch == 'Z'))) {
			fStringBuffer.append((char)ch);
			ch = get_ch();
		}
		
		return ch;
	}
	
	private int get_ch() {
		int ch = fScanner.get_ch();
		
		// Convert all '\r' sequences to '\n'
		if (ch == '\r') {
			int ch2 = fScanner.get_ch();
			if (ch2 != '\n') {
				fScanner.unget_ch(ch2);
			}
			ch = '\n';
		}
		
		return ch; 
	}
	
	private void unget_ch(int ch) {
		fScanner.unget_ch(ch);
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}

	private void error(String msg) throws SVParseException {
		endCapture();
		fParser.error(msg);
	}
}

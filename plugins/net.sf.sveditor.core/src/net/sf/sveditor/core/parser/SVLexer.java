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
import java.util.Set;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVLexer {
	private ITextScanner				fScanner;
	private Set<String>					f2SeqPrefixes;
	private Set<String>					f3SeqPrefixes;
	private Set<String>					fOperatorSet;
	private Set<String>					fKeywordSet;
	
	private String						fImage;
	private boolean						fIsString;
	private boolean						fIsOperator;
	private boolean						fIsNumber;
	private boolean						fIsIdentifier;
	private boolean						fIsKeyword;
	private boolean						fTokenConsumed;
	private boolean						fNewlineAsOperator;
	
	private StringBuilder				fStringBuffer;
	private boolean						fDebugEn = false;
	private boolean						fEOF;
	
	private StringBuilder				fCaptureBuffer;
	private boolean						fCapture;
	
	private boolean						fEnableEOFException = true;
	
	private ISVParser					fParser;
	private SVDBLocation				fStartLocation;
	
	private static String operators[] = {
		"(", ")", "{", "}", "[", "]",
		"&", "&&", "|", "||", 
		"-", "--", "+", "++",
		"%", "!", "*", "/", "^", "~", "?", "@",
		"<", "<<", "<=",
		">", ">>", ">=",
		":", "::", ":/", ":=",
		",", ";", ".", ":",
		"->",
		"=", "*=", "/=", "%=", "+=", "==", "!=",
		"-=", "<<=", ">>=", "&=", "^=", "|=", "#"
	};
	
	public SVLexer() {
		f2SeqPrefixes = new HashSet<String>();
		f3SeqPrefixes = new HashSet<String>();
		fOperatorSet  = new HashSet<String>();
		
		fKeywordSet = new HashSet<String>();

		fStringBuffer = new StringBuilder();
		fCaptureBuffer = new StringBuilder();
		fCapture = false;
		
		for (String op : operators) {
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
	
	/**
	 * Returns the start location of the active token
	 * 
	 * @return
	 */
	public SVDBLocation getStartLocation() {
		return fStartLocation;
	}
	
	public void enableEOFException(boolean en) {
		fEnableEOFException = en;
	}
	
	public void setNewlineAsOperator(boolean en) {
		fNewlineAsOperator = en;
	}
	
	public void init(ISVParser parser, ITextScanner scanner) {
		fParser = parser;
		fTokenConsumed = true;
		fScanner = scanner; // parser.scanner();
		fEOF = false;
	}
	
	public void parseException(String msg) throws SVParseException {
		// TODO: get filename
		ScanLocation loc = fScanner.getLocation();
		throw SVParseException.createParseException(msg, loc.getFileName(), loc.getLineNo());
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
	
	public void pushKeyword(String id) {
		fIsKeyword = true;
		fImage = id;
		fTokenConsumed = false;
	}
	
	public boolean isIdentifier() {
		peek();
		return fIsIdentifier;
	}
	
	public boolean isNumber() {
		peek();
		return fIsNumber;
	}
	
	public boolean isKeyword() {
		peek();
		return fIsKeyword;
	}
	
	public String getImage() {
		return fImage;
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
			
			parseException("Expecting one of operator \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		return eatToken();
	}

	public boolean peekKeyword(String ... kw) throws SVParseException {
		peek();
		
		boolean found = false;
		if (fIsKeyword) {
			if (kw.length == 0) {
				found = true;
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
	
	public String readKeyword(String ... kw) throws SVParseException {
		
		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();
			
			for (int i=0; i<kw.length; i++) {
				sb.append(kw[i]);
				if (i+1 < kw.length) {
					sb.append(", ");
				}
			}
			
			parseException("Expecting one of keyword \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		return eatToken();
	}
	
	public String eatToken() {
		peek();
		if (fCapture) {
			if (fCaptureBuffer.length() > 0) {
				fCaptureBuffer.append(" ");
			}
			fCaptureBuffer.append(fImage);
		}
		fTokenConsumed = true;
		return fImage;
	}
	
	public String readString() throws SVParseException {
		peek();
		
		if (!fIsString) {
			parseException("Expecting a string ; received \"" +
					fImage + "\"");
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
			parseException("Expecting an identifier ; received \"" + 
					fImage + "\"");
		}
		
		return eatToken();
	}
	
	public String readIdOrKeyword() throws SVParseException {
		peek();

		if (!fIsIdentifier && !fIsKeyword) {
			parseException("Expecting an identifier or keyword ; received \"" + 
					fImage + "\"");
		}
		
		return eatToken();
	}

	public String readNumber() throws SVParseException {
		peek();

		if (!fIsNumber) {
			parseException("Expecting a number ; received \"" + 
					fImage + "\"");
		}

		return eatToken();
	}
	
	private boolean next_token() {
		if (fEOF) {
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
			return next_token_int();
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
		fCapture = false;
		return fCaptureBuffer.toString();
	}
	
	private boolean next_token_int() throws SVParseException {
		int ch = get_ch();
		int ch2 = -1;
		
		fIsOperator    = false;
		fIsNumber      = false;
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
		fStartLocation = new SVDBLocation(loc.getLineNo(), -1);

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
			fStringBuffer.append((char)ch);
			while ((ch = get_ch()) != -1) {
				if (ch == '"' && last_ch != '\\') {
					break;
				}
				fStringBuffer.append((char)ch);
				last_ch = ch;
			}
			
			if (ch != '"') {
				parseException("Unterminated string");
			}
			fStringBuffer.append((char)ch);
			fIsString = true;

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
				parseException("Bad partial operator: " + tmp);
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
		} else if (ch == '\'' || (ch >= '0' && ch <= '9')) {
			
			if (ch == '\'') {
				fStringBuffer.append((char)ch);
				ch = get_ch();
				
				if (ch == -1) {
					parseException("unexpected EOF after \"'\"");
				}
				fStringBuffer.append((char)ch);
				
				// TODO: probably should be more selective here
				while ((ch = get_ch()) != -1 && 
						((ch >= '0' && ch <= '9') ||
						 (ch >= 'a' && ch <= 'f') ||
						 (ch >= 'A' && ch <= 'F'))) {
					fStringBuffer.append((char)ch);
				}
			} else {
				// Possibly a base...
				fStringBuffer.append((char)ch);
				
				while ((ch = get_ch()) != -1 && 
						(ch >= '0' && ch <= '9')) {
					fStringBuffer.append((char)ch);
				}
				
				if (ch == '\'') {
					fStringBuffer.append((char)ch);
					
					// read the format character
					fStringBuffer.append((char)get_ch());
					
					// read balance of the number
					while ((ch = get_ch()) != -1 && 
							((ch >= '0' && ch <= '9') ||
							 (ch >= 'a' && ch <= 'f') ||
							 (ch >= 'A' && ch <= 'F'))) {
						fStringBuffer.append((char)ch);
					}
				}
			}
			
			
			if (ch != -1) {
				unget_ch(ch);
			}

			fIsNumber = true;
		}
		
		if (fStringBuffer.length() == 0) {
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
					fIsIdentifier = false;
				}
			}
			fTokenConsumed = false;
			debug("next_token(): \"" + fImage + "\"");
			return true;
		}
	}
	
	private int get_ch() {
		int ch = fScanner.get_ch();
		
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

}

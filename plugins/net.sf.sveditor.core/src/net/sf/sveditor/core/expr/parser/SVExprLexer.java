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


package net.sf.sveditor.core.expr.parser;

import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.scanner.SVKeywords;

public class SVExprLexer {
	private int 						fUngetCh;
	private InputStream					fInput;
	private byte						fBuffer[];
	private int							fBufferIdx;
	private int							fBufferMax;
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
	
	private StringBuilder				fStringBuffer;
	private boolean						fDebugEn;
	
	private static String operators[] = {
		"(", ")", "{", "}", "[", "]",
		"&", "&&", "|", "||", 
		"-", "--", "+", "++",
		"%", "!", "*", "/",
		"<", "<<", "<=",
		">", ">>", ">=",
		":", ":/", ":=",
		",", ";", ".", ":",
		"->",
		"=", "*=", "/=", "%=", "+=", "==", "!=",
		"-=", "<<=", ">>=", "&=", "^=", "|="
		
	};
	
	private static String keywords[] = {
		"super", "this", "new",
		"if", "else", "solve", "before", "foreach", "dist",
		"inside",
		"wildcard", "iff", "bins", "illegal_bins", "ignore_bins",
		"default", "sequence"
	};
	
	public SVExprLexer() {
		fBuffer = new byte[1024*1024];
		
		f2SeqPrefixes = new HashSet<String>();
		f3SeqPrefixes = new HashSet<String>();
		fOperatorSet  = new HashSet<String>();
		
		fKeywordSet = new HashSet<String>();

		fStringBuffer = new StringBuilder();
		
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
		fDebugEn = false;
	}
	
	public void init(InputStream in) {
		fTokenConsumed = true;
		fUngetCh = -1;
		fInput   = in;
		fBufferIdx = 0;
		fBufferMax = 0;
	}
	
	public String peek() throws SVExprLexerException {
		if (fTokenConsumed) {
			next_token();
			debug("peek() -- \"" + fImage + "\"");
		}
		return fImage;
	}
	
	public boolean isIdentifier() {
		return fIsIdentifier;
	}
	
	public boolean isNumber() {
		return fIsNumber;
	}
	
	public String getImage() {
		return fImage;
	}
	
	public boolean peekOperator(String ... ops) throws SVExprLexerException {
		peek();
		
		if (fIsOperator) {
			for (String op : ops) {
				if (fImage.equals(op)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public boolean peekId() throws SVExprLexerException {
		peek();
		
		return fIsIdentifier;
	}
	
	public boolean peekNumber() throws SVExprLexerException {
		peek();
		
		return fIsNumber;
	}
	
	public String readOperator(String ... ops) throws SVExprLexerException {
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
			
			throw new SVExprLexerException("Expecting one of operator \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		fTokenConsumed = true;
		return fImage;
	}

	public boolean peekKeyword(String ... kw) throws SVExprLexerException {
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
	
	public String readKeyword(String ... kw) throws SVExprLexerException {
		
		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();
			
			for (int i=0; i<kw.length; i++) {
				sb.append(kw[i]);
				if (i+1 < kw.length) {
					sb.append(", ");
				}
			}
			
			throw new SVExprLexerException("Expecting one of keyword \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		fTokenConsumed = true;
		return fImage;
	}
	
	public String eatToken() {
		fTokenConsumed = true;
		return fImage;
	}
	
	public String readString() throws SVExprLexerException {
		peek();
		
		if (!fIsString) {
			throw new SVExprLexerException("Expecting a string ; received \"" +
					fImage + "\"");
		}
		fTokenConsumed = true;
		
		return fImage;
	}

	public boolean peekString() throws SVExprLexerException {
		peek();
		
		return fIsString;
	}

	public String readId() throws SVExprLexerException {
		peek();

		if (!fIsIdentifier) {
			throw new SVExprLexerException("Expecting an identifier ; received \"" + 
					fImage + "\"");
		}
		fTokenConsumed = true;
		return fImage;
	}
	
	public String readNumber() throws SVExprLexerException {
		peek();

		if (!fIsNumber) {
			throw new SVExprLexerException("Expecting a number ; received \"" + 
					fImage + "\"");
		}

		fTokenConsumed = true;
		return fImage;
	}
	
	public void next_token() throws SVExprLexerException {
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
			} else if (!Character.isWhitespace(ch)) {
				break;
			}
			ch = get_ch();
		}
		fStringBuffer.setLength(0);
		String tmp = "" + (char)ch;

		if (ch == '"') {
			// String
			while ((ch = get_ch()) != -1 && ch != '"') {
				fStringBuffer.append((char)ch);
			}
			
			if (ch != '"') {
				throw new SVExprLexerException("Unterminated string");
			}
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
				throw new SVExprLexerException("Bad partial operator: " + tmp);
			}
			
		} else if (Character.isJavaIdentifierStart(ch)) {
			// Identifier or keyword
			fStringBuffer.append((char)ch);
			while ((ch = get_ch()) != -1 && Character.isJavaIdentifierPart(ch)) {
				fStringBuffer.append((char)ch);
			}
			unget_ch(ch);
			fIsIdentifier = true;
		} else if (ch == '\'' || (ch >= '0' && ch <= '9')) {
			
			if (ch == '\'') {
				fStringBuffer.append((char)ch);
				ch = get_ch();
				
				if (ch == -1) {
					throw new SVExprLexerException("unexpected EOF after \"'\"");
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
			// throw new EOFException();
		}
		
		fImage = fStringBuffer.toString();
		
		if (fIsIdentifier) {
			if ((fIsKeyword = fKeywordSet.contains(fImage))) {
				fIsIdentifier = false;
			}
		}
		fTokenConsumed = false;
	}
	
	private int get_ch() {
		int ret = -1;
		
		if (fUngetCh != -1) {
			ret = fUngetCh;
			fUngetCh = -1;
		} else {
			if (fBufferIdx >= fBufferMax) {
				try {
					fBufferMax = fInput.read(fBuffer, 0, fBuffer.length);
					fBufferIdx = 0;
				} catch (IOException e) { }
			}
			
			if (fBufferIdx < fBufferMax) {
				ret = fBuffer[fBufferIdx++];
			}
		}
		
		return ret;
	}
	
	private void unget_ch(int ch) {
		fUngetCh = ch;
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}

}

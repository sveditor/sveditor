package net.sf.sveditor.core.constraint.parser;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ConstraintLexer {
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
	private boolean						fIsOperator;
	private boolean						fIsNumber;
	private boolean						fIsIdentifier;
	private boolean						fIsKeyword;
	private boolean						fTokenConsumed;
	
	private StringBuilder				fStringBuffer;
	
	private static String operators[] = {
		"(", ")", "{", "}", "[", "]",
		"&", "&&", "|", "||", 
		"-", "--", "+", "++",
		"%",
		"<", "<<", "<=",
		">", ">>", ">=",
		":", ":/", ":=",
		",", ";", ".",
		"->",
		"=", "*=", "/=", "%=", "+=", "==",
		"-=", "<<=", ">>=", "&=", "^=", "|="
		
	};
	
	private static String keywords[] = {
		"super", "this", "new",
		"if", "else", "solve", "before", "foreach", "dist"
	};
	
	public ConstraintLexer() {
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
		
		for (String kw : keywords) {
			fKeywordSet.add(kw);
		}
	}
	
	public void init(InputStream in) {
		fTokenConsumed = true;
		fUngetCh = -1;
		fInput   = in;
		fBufferIdx = 0;
		fBufferMax = 0;
	}
	
	public String peek() throws LexerException {
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
	
	public boolean peekOperator(String ... ops) throws LexerException {
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
	
	public boolean peekId() throws LexerException {
		peek();
		
		return fIsIdentifier;
	}
	
	public boolean peekNumber() throws LexerException {
		peek();
		
		return fIsNumber;
	}
	
	public String readOperator(String ... ops) throws LexerException {
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
			
			throw new LexerException("Expecting one of operator \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		fTokenConsumed = true;
		return fImage;
	}

	public boolean peekKeyword(String ... kw) throws LexerException {
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
	
	public String readKeyword(String ... kw) throws LexerException {
		
		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();
			
			for (int i=0; i<kw.length; i++) {
				sb.append(kw[i]);
				if (i+1 < kw.length) {
					sb.append(", ");
				}
			}
			
			throw new LexerException("Expecting one of keyword \"" + 
					sb.toString() + "\" ; received \"" + fImage + "\"");
		}
		
		fTokenConsumed = true;
		return fImage;
	}
	
	public void eatToken() {
		fTokenConsumed = true;
	}

	public String readId() throws LexerException {
		peek();

		if (!fIsIdentifier) {
			throw new LexerException("Expecting an identifier ; received \"" + 
					fImage + "\"");
		}
		fTokenConsumed = true;
		return fImage;
	}
	
	public String readNumber() throws LexerException {
		peek();

		if (!fIsNumber) {
			throw new LexerException("Expecting a number ; received \"" + 
					fImage + "\"");
		}

		fTokenConsumed = true;
		return fImage;
	}
	
	public void next_token() throws LexerException {
		int ch = get_ch();
		int ch2 = -1;
		
		fIsOperator    = false;
		fIsNumber      = false;
		fIsIdentifier  = false;
		fIsKeyword     = false;
		
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

		// Operators that can have up to two elements
		if (fOperatorSet.contains(tmp) || 
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
			}
		
			if (!fIsOperator) {
				throw new LexerException("Bad partial operator: " + tmp);
			}
			
		} else if (Character.isJavaIdentifierPart(ch)) {
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
					throw new LexerException("unexpected EOF after \"'\"");
				}
				fStringBuffer.append((char)ch);
			}
			
			// TODO: probably should be more selective here
			while ((ch = get_ch()) != -1 && 
					((ch >= '0' && ch <= '9') ||
					 (ch >= 'a' && ch <= 'f') ||
					 (ch >= 'A' && ch <= 'F'))) {
				fStringBuffer.append(ch);
			}
			
			if (ch != -1) {
				unget_ch(ch);
			}

			fIsNumber = true;
		}
		
		if (fStringBuffer.length() == 0) {
			throw new EOFException();
		}
		
		fImage = fStringBuffer.toString();
		
		if (fIsIdentifier) {
			fIsKeyword = fKeywordSet.contains(fImage);
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
		System.out.println(msg);
	}

}

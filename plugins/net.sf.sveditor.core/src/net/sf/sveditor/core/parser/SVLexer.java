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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVLexer extends SVToken {
	private ITextScanner fScanner;
	// 2- and 3-character operator prefixes
	private Set<String>	fSeqPrefixes[];
	private Set<String> fOperatorSet;
	private Set<String> fKeywordSet;

	private List<ISVTokenListener> fTokenListeners;

	private boolean fTokenConsumed;
	private boolean fNewlineAsOperator;

	private StringBuilder fStringBuffer;
	private static final boolean fDebugEn = false;
	private boolean fEOF;

	private StringBuilder fCaptureBuffer;
	private boolean fCapture;
	private SVToken fCaptureLastToken;
	private ISVParser fParser;
	private Stack<SVToken> fUngetStack;
	private boolean fInAttr;
	private LogHandle			fLog;

	public static final String RelationalOps[] = { "&", "&&", "|", "||", "-",
			"+", "%", "!", "*", "**", "/", "^", "^~", "~^", "~",
			"?", "<", "<<", "<=", "<<<", ">", ">>", ">=", ">>>", "=", "*=",
			"/=", "%=", "+=", "==", "!=", "-=", "<<=", ">>=", "<<<=", ">>>=",
			"&=", "^=", "|=", "===", "!==", "==?", "!=?"};

	public static final String GroupingOps[] = { "(", ")", "{", "}", "[", "]", };

	public static final String MiscOps[] = { ":", "::", ":/", ":=", "+:", "-:", // array-index
																				// operators
			",", ";", ".", ".*", "'", "->", "-->", "#", "##", "@", "@@", "(*", "*)",
			// Assertion operators
			"|=>", "|->", "#-#", "#=#", "##",
			"--", "++"};

	private static final String AllOperators[];

	static {
		AllOperators = new String[RelationalOps.length + GroupingOps.length
				+ MiscOps.length];
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

	@SuppressWarnings("unchecked")
	public SVLexer() {
		fLog = LogFactory.getLogHandle("SVLexer");
		fOperatorSet = new HashSet<String>();
		fSeqPrefixes = new Set[] {
			fOperatorSet,
			new HashSet<String>(),
			new HashSet<String>()
		};

		fKeywordSet = new HashSet<String>();

		fStringBuffer = new StringBuilder();
		fCaptureBuffer = new StringBuilder();
		fCapture = false;

		fUngetStack = new Stack<SVToken>();

		fTokenListeners = new ArrayList<ISVTokenListener>();

		for (String op : AllOperators) {
			if (op.length() == 3) {
				fSeqPrefixes[1].add(op.substring(0,2));
				fSeqPrefixes[2].add(op.substring(0,3));
			} else if (op.length() == 2) {
				fSeqPrefixes[1].add(op.substring(0,2));
			}
			fOperatorSet.add(op);
		}

		for (String kw : SVKeywords.getKeywords()) {
			if (kw.endsWith("*")) {
				kw = kw.substring(0, kw.length() - 1);
			}
			fKeywordSet.add(kw);
		}
		fEOF = false;
	}

	public void addTokenListener(ISVTokenListener l) {
		fTokenListeners.add(l);
	}

	public void removeTokenListener(ISVTokenListener l) {
		fTokenListeners.remove(l);
	}

	public void setNewlineAsOperator(boolean en) {
		fNewlineAsOperator = en;
	}

	public void setInAttr(boolean in) {
		fInAttr = in;
	}

	public void init(ISVParser parser, ITextScanner scanner) {
		fTokenConsumed = true;
		fScanner = scanner;
		fEOF = false;
		fParser = parser;
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

		if (fTokenListeners.size() > 0) {
			for (ISVTokenListener l : fTokenListeners) {
				l.ungetToken(tok);
			}
		}

		fUngetStack.push(tok);
		peek();
		if (fDebugEn) {
			debug("After un-get of token \"" + tok.getImage()
					+ "\" next token is \"" + peek() + "\"");
		}
	}

	public void ungetToken(List<SVToken> tok_l) {
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

	public boolean peekOperator(String... ops) throws SVParseException {
		peek();

		if (fIsOperator) {
			if (ops.length == 0) {
				return true;
			} else if (ops.length == 1) {
				return fImage.equals(ops[0]);
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

	public String readOperator(String... ops) throws SVParseException {
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

			for (int i = 0; i < ops.length; i++) {
				sb.append(ops[i]);
				if (i + 1 < ops.length) {
					sb.append(", ");
				}
			}

			error("Expecting one of operator \"" + sb.toString()
					+ "\" ; received \"" + fImage + "\"");
		}

		return eatToken();
	}

	public boolean peekKeyword(String... kw) throws SVParseException {
		peek();

		boolean found = false;
		if (fIsKeyword) {
			if (kw.length == 0) {
				found = true;
			} else if (kw.length == 1) {
				found = fImage.equals(kw[0]);
			} else if (kw.length == 2) {
				found = fImage.equals(kw[0]) || fImage.equals(kw[1]);
			} else if (kw.length == 3) {
				found = fImage.equals(kw[0]) || fImage.equals(kw[1])
						|| fImage.equals(kw[2]);
			} else if (kw.length == 4) {
				found = fImage.equals(kw[0]) || fImage.equals(kw[1])
						|| fImage.equals(kw[2]) || fImage.equals(kw[3]);
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
				sb.setLength(sb.length() - 2);
			}

			error("Expecting one of keyword \"" + sb.toString()
					+ "\" ; received \"" + fImage + "\"");
		}
		return eatToken();
	}

	public String readKeyword(String... kw) throws SVParseException {

		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();

			for (int i = 0; i < kw.length; i++) {
				sb.append(kw[i]);
				if (i + 1 < kw.length) {
					sb.append(", ");
				}
			}

			error("Expecting one of keyword \"" + sb.toString()
					+ "\" ; received \"" + fImage + "\"");
		}

		return eatToken();
	}

	public SVToken readKeywordTok(String... kw) throws SVParseException {

		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();

			for (int i = 0; i < kw.length; i++) {
				sb.append(kw[i]);
				if (i + 1 < kw.length) {
					sb.append(", ");
				}
			}

			error("Expecting one of keyword \"" + sb.toString()
					+ "\" ; received \"" + fImage + "\"");
		}

		return consumeToken();
	}

	public String eatToken() {
		peek();
		if (fCapture) {
			if (fCaptureBuffer.length() > 0
					&& ((isIdentifier() && fCaptureLastToken.isIdentifier()) || (isNumber() && fCaptureLastToken
							.isNumber()))) {
				fCaptureBuffer.append(" ");
			}
			fCaptureBuffer.append(fImage);
			fCaptureLastToken = duplicate(); // copy token
		}
		if (fTokenListeners.size() > 0) {
			SVToken tok = this.duplicate();
			for (ISVTokenListener l : fTokenListeners) {
				l.tokenConsumed(tok);
			}
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
			error("Expecting an identifier or keyword ; received \"" + fImage
					+ "\"");
		}

		return eatToken();
	}

	public String readNumber() throws SVParseException {
		peek();

		if (!fIsNumber) {
			error("Expecting a number ; received \"" + fImage + "\"");
		}

		return eatToken();
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
		int ch = get_ch();
		int ch2 = -1;

		fIsOperator = false;
		fIsNumber = false;
		fIsTime = false;
		fIsIdentifier = false;
		fIsKeyword = false;
		fIsString = false;

		// Skip whitespace and comments
		while (true) {
			if (ch == '/') {
				ch2 = get_ch();

				if (ch2 == '/') {
					while ((ch = get_ch()) != -1 && ch != '\n') {
					}
				} else if (ch2 == '*') {
					int end_comment[] = { -1, -1 };

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
				if (!Character.isWhitespace(ch)
						|| (ch == '\n' && fNewlineAsOperator)) {
					break;
				}
			}
			ch = get_ch();
		}
		fStringBuffer.setLength(0);
		if (ch != -1 && ch != 0xFFFF) {
			append_ch(ch);
		}

		// TODO: should fix
		ScanLocation loc = fScanner.getLocation();
		fStartLocation = new SVDBLocation(loc.getLineNo(), loc.getLinePos());

		if (ch == -1) {
			fEOF = true;
			/*
			 * if (fEnableEOFException) { throw new EOFException(); }
			 */
		} else if (fNewlineAsOperator && ch == '\n') {
			fIsOperator = true;
		} else if (ch == '"') {
			int last_ch = -1;
			// String
			fStringBuffer.setLength(0);
			while ((ch = get_ch()) != -1) {
				if (ch == '"' && last_ch != '\\') {
					break;
				}
				append_ch(ch);
				if (last_ch == '\\' && ch == '\\') {
					// Don't count a double quote
					last_ch = -1;
				} else {
					last_ch = ch;
				}
			}

			if (ch != '"') {
				error("Unterminated string");
			}
			fIsString = true;
		} else if (ch == '\'' || (ch >= '0' && ch <= '9')) {
			fIsNumber = true;

			if (ch == '\'') {
				ch2 = get_ch();
				if (isUnbasedUnsizedLiteralChar(ch2)) {
					// unbased_unsigned_literal
					// nothing more to do
					append_ch(ch2);
				} else if (isBaseChar(ch2)) {
					ch = readBasedNumber(ch2);
					unget_ch(ch);
				} else {
					unget_ch(ch2);
					fIsOperator = true;
				}
			} else {
				readNumber(ch);
			}

			fImage = fStringBuffer.toString();
		} else if (ch == '(') {
			// Could be (, (*
			// Want to avoid (*) case
			ch2 = get_ch();
			if (ch2 == '*') {
				int ch3 = get_ch();
				if (ch3 != ')') {
					append_ch('*');
					unget_ch(ch3);
				} else {
					unget_ch(ch3);
					unget_ch(ch2);
				}
			} else {
				unget_ch(ch2);
			}
			fIsOperator = true;
		} else if (ch == '*') {
			// Could be *, **, *=, or *)
			ch2 = get_ch();

			if (ch2 == ')' && fInAttr) {
				append_ch(')');
			} else if (ch2 == '*' || ch2 == '=') {
				append_ch(ch2);
			} else {
				unget_ch(ch2);
			}
			fIsOperator = true;
		} else if (fOperatorSet.contains(fStringBuffer.toString()) ||
				// Operators that can have up to three elements
				fSeqPrefixes[1].contains(fStringBuffer.toString()) ||
				fSeqPrefixes[2].contains(fStringBuffer.toString())) {
			// Probably an operator in some form
			operator();
		} else if (SVCharacter.isSVIdentifierStart(ch)) {
			// Identifier or keyword
			while ((ch = get_ch()) != -1 && SVCharacter.isSVIdentifierPart(ch)) {
				append_ch(ch);
			}
			unget_ch(ch);
			// Handle case where we received a single '$'
			if (fStringBuffer.length() == 1 && fStringBuffer.charAt(0) == '$') {
				fIsOperator = true;
			} else {
				fIsIdentifier = true;
			}
		} else if (ch == '\\') {
			// Escaped identifier
			while ((ch = get_ch()) != -1 && !Character.isWhitespace(ch)) {
				append_ch(ch);
			}
			unget_ch(ch);
		}

		if (fStringBuffer.length() == 0 && !fIsString) {
			fEOF = true;
			/*
			 * if (fEnableEOFException) { throw new EOFException(); }
			 */
			if (fDebugEn) {
				debug("EOF - " + getStartLocation().toString());
			}
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
			if (fDebugEn) {
				debug("next_token(): \"" + fImage + "\"");
			}
			return true;
		}
	}
	
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

	private void operator() throws SVParseException {
		int ch;
		int op_idx=0; // index of the op prefix to check
		
		if (fDebugEn) {
			debug("operator: " + fStringBuffer.toString());
		}
		while (op_idx < 2) {
			// Add a character and check whether is a prefix for the next
			// sequence
			if ((ch = get_ch()) != -1) {
				append_ch(ch);
				if (fDebugEn) {
					debug("  append: " + (char)ch + "  => " + fStringBuffer.toString());
				}
				if (!fSeqPrefixes[op_idx+1].contains(fStringBuffer.toString()) &&
						!fOperatorSet.contains(fStringBuffer.toString())) {
					// Doesn't match, so don't move forward
					unget_ch(ch);
					fStringBuffer.setLength(fStringBuffer.length()-1);
					if (fDebugEn) {
						debug("  \"" + (char)ch + "\" doesn't match");
					}
					break;
				} else {
					if (fDebugEn) {
						debug("  " + (char)ch + " does match -- " + fStringBuffer.toString());
					}
				}
			} else {
				break;
			}
			
			op_idx++;
		}

		if (fDebugEn) {
			debug("< operator: " + fStringBuffer.toString());
		}
		fIsOperator = true;
		if (!fOperatorSet.contains(fStringBuffer.toString())) {
			error("Problem with operator: " + fStringBuffer.toString());
		}
		
		/*
		if (f2SeqPrefixes.contains(fStringBuffer.toString())) {
			// Peek forward to see if the 2-wise sequence is present
			if ((ch2 = get_ch()) != -1) {
				fStringBuffer.append((char)ch2);
				if (fOperatorSet.contains(fStringBuffer.toString())) {
					if ((ch2 = get_ch()) != -1) {
						fStringBuffer.append((char)ch2);
						if (fOperatorSet.contains(fStringBuffer.toString())) {
							fIsOperator = true;
						} else {
							unget_ch(ch2);
							fStringBuffer.setLength(fStringBuffer.length()-1);
							fIsOperator = true;
						}
					}
				} else {
					unget_ch(ch2);
					fStringBuffer.append((char)ch)
					tmp = "" + (char) ch;
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
		 */
	}
	
	private static boolean isBaseChar(int ch) {
		return (ch == 's' || ch == 'S' || ch == 'd' || ch == 'D' || ch == 'b'
				|| ch == 'B' || ch == 'o' || ch == 'O' || ch == 'h' || ch == 'H');
	}

	private static boolean isUnbasedUnsizedLiteralChar(int ch) {
		return (ch == '0' || ch == '1' || ch == 'z' || ch == 'Z' || ch == 'x' || ch == 'X');
	}

	private static boolean isTimeUnitChar(int ch) {
		return (ch == 'f' || ch == 'p' || ch == 'n' || ch == 'u' || ch == 'm' || ch == 's');
	}

	// Enter on base digit
	private int readBasedNumber(int ch) throws SVParseException {
		int base;

		append_ch(ch);
		if (ch == 's' || ch == 'S') {
			ch = get_ch();
			append_ch(ch);
		}

		if (!isBaseChar(ch)) {
			error("Unknown base digit " + (char) ch);
		}
		base = Character.toLowerCase(ch);

		// Skip whitespace
		while ((ch = get_ch()) != -1 && Character.isWhitespace(ch)) {
		}

		if (base == 'd') {
			ch = readDecNumber(ch);
		} else if (base == 'h') {
			ch = readHexNumber(ch);
		} else if (base == 'o') {
			ch = readOctNumber(ch);
		} else if (base == 'b') {
			ch = readBinNumber(ch);
		}

		return ch;
	}

	/**
	 * On entry, have a decimal digit
	 * 
	 * @param ch
	 * @return
	 * @throws SVParseException
	 */
	private void readNumber(int ch) throws SVParseException {

		// Could be:
		// <number>
		// <size>'<base><number>
		// <number>.<number>
		// <number><time_unit>
		
		// Remove character that was already added
		fStringBuffer.setLength(fStringBuffer.length()-1);
		ch = readDecNumber(ch);

		if (isTimeUnitChar(ch)) {
			// Avoid #1step. Looks alot like #1s
			if (ch == 's') {
				int ch2 = get_ch();
				if (SVCharacter.isSVIdentifierPart(ch2)) {
					unget_ch(ch2);
				} else {
					append_ch(ch);
					ch = ch2;
				}
			} else {
				ch = readTimeUnit(ch);
			}
		} else if (ch == '.' || ch == 'e' || ch == 'E') {
			ch = readRealNumber(ch);
		} else {
			while (ch != -1 && Character.isWhitespace(ch)) {
				ch = get_ch();
			}

			if (ch == '\'') {
				append_ch(ch);
				ch = readBasedNumber(get_ch());
			} else {
				// Really just a decimal number
			}
		}

		unget_ch(ch);
	}

	private static boolean isDecDigit(int ch) {
		return (ch >= '0' && ch <= '9');
	}

	private int readDecNumber(int ch) throws SVParseException {
		while (ch >= '0' && ch <= '9') {
			append_ch(ch);
			ch = get_ch();
		}
		return ch;
	}

	// enter on post-'.'
	private int readRealNumber(int ch) throws SVParseException {
		if (ch == '.') {
			append_ch(ch);
			ch = readDecNumber(get_ch());
		}

		if (ch == 'e' || ch == 'E') {
			append_ch(ch);
			ch = get_ch();
			if (ch == '-' || ch == '+') {
				append_ch(ch);
				ch = get_ch();
			}

			if (!isDecDigit(ch)) {
				error("Expecting exponent, received " + (char) ch);
			}
			ch = readDecNumber(ch);
		}

		// Might be a time unit
		if (isTimeUnitChar(ch)) {
			ch = readTimeUnit(ch);
		}

		return ch;
	}

	// Enter on time-unit char
	private int readTimeUnit(int ch) throws SVParseException {
		append_ch(ch);
		
		if (ch != 's') {
			ch = get_ch();

			if (ch != 's') {
				error("Malformed time unit n" + (char) ch);
			}
			append_ch(ch);
		}
		
		fIsTime = true;

		return get_ch();
	}

	private int readHexNumber(int ch) throws SVParseException {
		while (ch != -1
				&& ((ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f')
						|| (ch >= 'A' && ch <= 'F') || ch == '_' || ch == 'x'
						|| ch == 'X' || ch == 'z' || ch == 'Z' || ch == '?')) {
			append_ch(ch);
			ch = get_ch();
		}

		return ch;
	}

	private int readOctNumber(int ch) throws SVParseException {
		while (ch != -1
				&& ((ch >= '0' && ch <= '7') || ch == '_' || ch == 'x'
						|| ch == 'X' || ch == 'z' || ch == 'Z' || ch == '?')) {
			append_ch(ch);
			ch = get_ch();
		}

		return ch;
	}

	private int readBinNumber(int ch) throws SVParseException {
		while (ch != -1
				&& (ch == '0' || ch == '1' || ch == '_' || ch == 'x'
						|| ch == 'X' || ch == 'z' || ch == 'Z' || ch == '?')) {
			append_ch(ch);
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
			fLog.debug(msg);
		}
	}

	private void error(String msg) throws SVParseException {
		endCapture();
		setInAttr(false);
		fParser.error(msg);
	}
}

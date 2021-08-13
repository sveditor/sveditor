/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/

package org.sveditor.core.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.sveditor.core.scanner.SVCharacter;
import org.sveditor.core.scanutils.ITextScanner;

import com.sun.org.apache.xpath.internal.compiler.Keywords;

public class SVLexer extends SVToken implements ISVKeywords, ISVOperators {
	public enum Context {
		Default,
		Behavioral,
		Expression,
		Constraint
	}
	
	private ITextScanner 			fScanner;
	// 2- and 3-character operator prefixes
	private Set<String>				fSeqPrefixes[];
	private Set<String> 			fOperatorSet;
	private Map<String, KW>			fDefaultKeywordSet;
	private Map<String, KW>			fConstraintKeywordSet;
	private Map<String, KW>			fExprKeywordSet;

	private List<ISVTokenListener>	fTokenListeners;

	private boolean 				fTokenConsumed;
	private boolean 				fIsDelayControl;

	private StringBuilder 			fStringBuffer;
	private static final boolean 	fDebugEn = false;
	private boolean 				fEOF;

	private ISVParser 				fParser;
	private Stack<SVToken> 			fUngetStack;
	private boolean 				fInAttr;
	private LogHandle				fLog;
	private Context					fContext;
	private SVLanguageLevel			fLanguageLevel;


	
	public SVLexer() {
		this(SVLanguageLevel.SystemVerilog);
	}
	
	@SuppressWarnings("unchecked")
	public SVLexer(SVLanguageLevel level) {
		fLanguageLevel = level;
		
		fLog = LogFactory.getLogHandle("SVLexer");
		fOperatorSet = new HashSet<String>();
		fSeqPrefixes = new Set[] {
			fOperatorSet,
			new HashSet<String>(),
			new HashSet<String>()
		};

		fDefaultKeywordSet = new HashMap<String, KW>();
		fConstraintKeywordSet = new HashMap<String, KW>();
		fExprKeywordSet = new HashMap<String, KW>();

		fStringBuffer = new StringBuilder();

		fUngetStack = new Stack<SVToken>();

		fTokenListeners = new ArrayList<ISVTokenListener>();

		for (String op : SVOperators.AllOperators) {
			if (op.length() == 3) {
				fSeqPrefixes[1].add(op.substring(0,2));
				fSeqPrefixes[2].add(op.substring(0,3));
			} else if (op.length() == 2) {
				fSeqPrefixes[1].add(op.substring(0,2));
			}
			fOperatorSet.add(op);
		}

		for (ISVKeywords.KW kw : ISVKeywords.KW.values()) {
			switch (fLanguageLevel) {
				case SystemVerilog:
					if (kw.isSV() || !kw.isAMS()) {
						fDefaultKeywordSet.put(kw.getImg(), kw);
					}
					break;
					
				case VerilogAMS:
					if (!kw.isSV() || kw.isAMS()) {
						fDefaultKeywordSet.put(kw.getImg(), kw);
					}
					break;
					
				default:
				case Verilog2005:
					if (!kw.isSV() && !kw.isAMS()) {
						fDefaultKeywordSet.put(kw.getImg(), kw);
					}
					break;
			}
		}
	
		fConstraintKeywordSet.putAll(fDefaultKeywordSet);
		fExprKeywordSet.putAll(fDefaultKeywordSet);
		
		// Customize
		fDefaultKeywordSet.remove("soft");
		
		// Remove 'unique' from the Expression set, since
		// unique() is a supported function
		fExprKeywordSet.remove("unique");
		
		fEOF = false;
		
		setContext(Context.Default);
	}
	
	public Context setContext(Context ctxt) {
		Context old_ctxt = fContext;
		fContext = ctxt;
	
		// Re-evaluate the current 
		if (old_ctxt != ctxt && fIsIdentifier || fKeyword != null) {
			Map<String, ISVKeywords.KW> kw = getKeywords(ctxt);
		
			fKeyword = kw.get(fImage);
		}
		
		return old_ctxt;
	}
	
	public Context getContext() {
		return fContext;
	}

	public void addTokenListener(ISVTokenListener l) {
		fTokenListeners.add(l);
	}

	public void removeTokenListener(ISVTokenListener l) {
		fTokenListeners.remove(l);
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
		fKeyword = tok.fKeyword;
		fIsNumber = tok.fIsNumber;
		fOperator = tok.fOperator;
		fIsString = tok.fIsString;
		fIsTime = tok.fIsTime;
		fStartLocation = tok.fStartLocation;
	}

	// Returns a token
	public SVToken consumeToken() {
		SVToken tok = null;
		
		if (peek() != null) {
			tok = this.duplicate();
			eatToken();
		}

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
		return getImage();
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
		return (fKeyword != null);
	}

	public boolean isOperator() {
		peek();
		return (fOperator != null);
	}
	
	public boolean peekOperator() throws SVParseException {
		peek();
		
		return (fOperator != null);
	}
	
	public OP peekOperatorE() throws SVParseException {
		peek();
		
		return fOperator;
	}
	
	public boolean peekOperator(OP op) throws SVParseException {
		peek();
		return (fOperator == op);
	}
	
	public boolean peekOperator(OP op1, OP op2) throws SVParseException {
		peek();
		return (fOperator == op1 || fOperator == op2);
	}
	
	public boolean peekOperator(OP op1, OP op2, OP op3) throws SVParseException {
		peek();
		return (fOperator == op1 || fOperator == op2 || fOperator == op3);
	}

	public boolean peekOperator(OP op1, OP op2, OP op3, OP op4) throws SVParseException {
		peek();
		return (fOperator == op1 || fOperator == op2 || fOperator == op3 || fOperator == op4);
	}
	
	public boolean peekOperator(OP op1, OP op2, OP op3, OP op4, OP op5, OP op6) throws SVParseException {
		peek();
		return (fOperator == op1 || fOperator == op2 || fOperator == op3 || fOperator == op4 ||
				fOperator == op5 || fOperator == op6);
	}
	
	public boolean peekOperator(Set<OP> ops) throws SVParseException {
		peek();

		return ops.contains(fOperator);
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

		return eatTokenR();
	}
	
	public OP readOperator() throws SVParseException {
		peek();
		
		if (fOperator == null) {
			error("Expecting operator ; received \"" + getImage() + "\"");
		} else {
			OP op = fOperator;
			eatToken();
			return op;
		}
		return null;
	}
	
	public void readOperator(OP op) throws SVParseException {
		peek();
		
		if (fOperator != op) {
			error("Expecting operator \"" + op.getImg()
					+ "\" ; received \"" + getImage() + "\"");
		} else {
			eatToken();
		}
	}
	
	public OP readOperator(OP op1, OP op2) throws SVParseException {
		peek();
		
		if (fOperator != op1 && fOperator != op2) {
			error("Expecting operator \"" + op1.getImg()
					+ "\" or \"" + op2.getImg() + 
					"\"; received \"" + getImage() + "\"");
		} else {
			OP ret = fOperator;
			eatToken();
			return ret;
		}
		return null;
	}

	public OP readOperator(OP op1, OP op2, OP op3) throws SVParseException {
		peek();
		
		if (fOperator != op1 && fOperator != op2 && fOperator != op3) {
			error("Expecting operator " + op1.getImg() +
					", " + op2.getImg() + ", " + op3.getImg() + "; " +
					"received \"" + getImage() + "\"");
		} else {
			OP ret = fOperator;
			eatToken();
			return ret;
		}
		return null;
	}

	public boolean peekKeyword() throws SVParseException {
		peek();
		return (fKeyword != null);
	}
	
	public KW peekKeywordE() throws SVParseException {
		peek();
		return fKeyword;
	}

	public boolean peekKeyword(KW kw) throws SVParseException {
		peek();
		return (fKeyword != null && fKeyword == kw);
	}
	
	public boolean peekKeyword(KW kw1, KW kw2) throws SVParseException {
		peek();
		return (fKeyword != null && (fKeyword == kw1 || fKeyword == kw2));
	}
	
	public boolean peekKeyword(KW kw1, KW kw2, KW kw3) throws SVParseException {
		peek();
		return (fKeyword == kw1 || fKeyword == kw2 || fKeyword == kw3);
	}

	public boolean peekKeyword(KW ... kw) throws SVParseException {
		peek();

		if (fKeyword != null) {
			switch (kw.length) {
				case 0:
					return true;
				case 1:
					return fKeyword == kw[0];
				case 2:
					return (fKeyword == kw[0] || fKeyword == kw[1]);
				case 3:
					return (fKeyword == kw[0] || fKeyword == kw[1] || fKeyword == kw[2]);
				case 4:
					return (fKeyword == kw[0] || fKeyword == kw[1] || fKeyword == kw[2] ||
							fKeyword == kw[3]);
				case 5:
					return (fKeyword == kw[0] || fKeyword == kw[1] || fKeyword == kw[2] ||
							fKeyword == kw[3] || fKeyword == kw[4]);
				default:
					for (KW k : kw) {
						if (fKeyword == k) {
							return true;
						}
					}
					return false;
			}
		}

		return false;
	}

	public boolean peekKeyword(Set<KW> kw) throws SVParseException {
		peek();

		return kw.contains(fKeyword);
	}

	public KW readKeyword(Set<KW> kw_s) throws SVParseException {
		KW kw = peekKeywordE();
		if (!kw_s.contains(kw)) {
			StringBuilder sb = new StringBuilder();

			for (KW k : kw_s) {
				sb.append(k.getImg());
			}
			if (sb.length() > 2) {
				sb.setLength(sb.length() - 2);
			}

			error("Expecting one of keyword \"" + sb.toString()
					+ "\" ; received \"" + fImage + "\"");
		}
		
		KW ret = fKeyword;
		eatToken();
		return ret;
	}
	
	public String readKeyword() throws SVParseException {
		peek();
		if (fKeyword == null) {
			error("Expecting a keyword. Received \"" + fImage + "\"");
		}
		return eatTokenR();
	}
	
	public KW readKeywordE() throws SVParseException {
		peek();
		if (fKeyword == null) {
			error("Expecting a keyword. Received \"" + getImage() + "\"");
		}
		KW ret = fKeyword;
		eatToken();
		return ret;
	}
	
	public String readKeyword(KW kw) throws SVParseException {
		if (!peekKeyword(kw)) {
			error("Expecting keyword \"" + kw.getImg()
					+ "\" ; received \"" + fImage + "\"");
		}
		return eatTokenR();
	}
	
	public KW readKeyword(KW kw1, KW kw2) throws SVParseException {
		if (!peekKeyword(kw1, kw2)) {
			error("Expecting keyword \"" + kw1.getImg() + "\" or \"" + kw2.getImg() + 
					"\" ; received \"" + fImage + "\"");
		}
		KW kw = fKeyword;
		eatToken();
		return kw;
	}

	public KW readKeyword(KW kw1, KW kw2, KW kw3) throws SVParseException {
		if (!peekKeyword(kw1, kw2, kw3)) {
			error("Expecting keywords " + 
					kw1.getImg() + " " +
					kw2.getImg() + " " + 
					kw3.getImg() + " " + 
					"; received \"" + getImage() + "\"");
		}
		KW kw = fKeyword;
		eatToken();
		return kw;
	}	
	
	public KW readKeyword(KW kw1, KW kw2, KW kw3, KW kw4) throws SVParseException {
		if (!peekKeyword(kw1, kw2, kw3, kw4)) {
			error("Expecting keywords " + 
					kw1.getImg() + " " +
					kw2.getImg() + " " + 
					kw3.getImg() + " " + 
					kw4.getImg() + " " + 
					"; received \"" + getImage() + "\"");
		}
		KW kw = fKeyword;
		eatToken();
		return kw;
	}	

	public KW readKeyword(KW ... kw) throws SVParseException {

		if (!peekKeyword(kw)) {
			StringBuilder sb = new StringBuilder();

			for (int i = 0; i < kw.length; i++) {
				sb.append(kw[i].getImg());
				if (i + 1 < kw.length) {
					sb.append(", ");
				}
			}

			error("Expecting one of keyword \"" + sb.toString()
					+ "\" ; received \"" + getImage() + "\"");
		}

		KW ret = fKeyword;
		eatToken();
		return ret;
	}

	public void eatToken() {
		peek();
		if (fTokenListeners.size() > 0) {
			for (ISVTokenListener l : fTokenListeners) {
				l.tokenConsumed(this);
			}
		}
		fTokenConsumed = true;
	}

	public String eatTokenR() {
		peek();
		if (fTokenListeners.size() > 0) {
			for (ISVTokenListener l : fTokenListeners) {
				l.tokenConsumed(this);
			}
		}
		fTokenConsumed = true;
		return getImage();
	}
	
	public String readString() throws SVParseException {
		peek();

		if (!fIsString) {
			error("Expecting a string ; received \"" + getImage() + "\"");
		}

		return eatTokenR();
	}

	public boolean peekString() throws SVParseException {
		peek();

		return fIsString;
	}

	public String readId() throws SVParseException {
		peek();

		if (!fIsIdentifier) {
			error("Expecting an identifier ; received \"" + getImage() + "\"");
		}

		return eatTokenR();
	}

	public SVToken readIdTok() throws SVParseException {
		peek();

		if (!fIsIdentifier) {
			error("Expecting an identifier ; received \"" + getImage() + "\"");
		}

		return consumeToken();
	}

	public String readIdOrKeyword() throws SVParseException {
		peek();

		if (!fIsIdentifier && (fKeyword == null)) {
			error("Expecting an identifier or keyword ; received \"" + getImage()
					+ "\"");
		}

		return eatTokenR();
	}

	public String readNumber() throws SVParseException {
		peek();

		if (!fIsNumber) {
			error("Expecting a number ; received \"" + getImage() + "\"");
		}

		return eatTokenR();
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

	private boolean next_token_int() throws SVParseException {
		int ch = fScanner.get_ch();
		int ch2 = -1;
		
		if (fDebugEn) {
			fLog.debug("--> next_token_int()");
		}

		fOperator = null;
		fIsNumber = false;
		fIsTime = false;
		fIsIdentifier = false;
		boolean escaped_id = false;
		fKeyword = null;
		fIsString = false;
		boolean local_is_delay_ctrl = fIsDelayControl;
		fIsDelayControl = false;

		/*
		// Skip whitespace and comments
		while ((ch = fScanner.get_ch()) != -1 && 
				Character.isWhitespace(ch)) { }
		 */
		
		while (true) {
			if (ch == '/') {
				ch2 = fScanner.get_ch();

				if (ch2 == '/') {
					while ((ch = fScanner.get_ch()) != -1 && ch != '\n') {
					}
				} else if (ch2 == '*') {
					int end_comment[] = { -1, -1 };

					while ((ch = fScanner.get_ch()) != -1) {
						end_comment[0] = end_comment[1];
						end_comment[1] = ch;

						if (end_comment[0] == '*' && end_comment[1] == '/') {
							break;
						}
					}

					ch = ' ';
				} else {
					fScanner.unget_ch(ch2);
					break;
				}
			} else if (ch == '`') {
				// Very likely an `undefined operator, but let's check
				fStringBuffer.setLength(0);
				while ((ch = fScanner.get_ch()) != -1 && SVCharacter.isSVIdentifierPart(ch)) {
					fStringBuffer.append((char)ch);
				}
				fScanner.unget_ch(ch);
			
//				String tok = fStringBuffer.toString();
				
				if (fContext == Context.Behavioral) {
					// Return ';' in a behavioral scope to prevent extraneous errors
					fOperator = OP.SEMICOLON;
					fTokenConsumed = false;
					return true;
				} else {
					// treat as whitespace
					continue;
				}				
			} else {
				if (!Character.isWhitespace(ch)) {
					break;
				}
			}
			ch = fScanner.get_ch();
		}

		fStringBuffer.setLength(0);
		if (ch != -1 && ch != 0xFFFF) {
			append_ch(ch);
		}

		fStartLocation = SVDBLocation.pack(
				fScanner.getFileId(),
				fScanner.getLineno(),
				fScanner.getLinepos());

		if (ch == -1) {
			fEOF = true;
			/*
			 * if (fEnableEOFException) { throw new EOFException(); }
			 */
		} else if (ch == '"') {
			int last_ch = -1;
			// String
			fStringBuffer.setLength(0);
			while ((ch = fScanner.get_ch()) != -1) {
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
				ch2 = fScanner.get_ch();
				if (isUnbasedUnsizedLiteralChar(ch2)) {
					// unbased_unsigned_literal
					// nothing more to do
					append_ch(ch2);
				} else if (isBaseChar(ch2)) {
					ch = readBasedNumber(ch2);
					fScanner.unget_ch(ch);
				} else {
					fScanner.unget_ch(ch2);
					fOperator = OP.SQUOTE;
				}
			} else {
				readNumber(ch, local_is_delay_ctrl);
				ch = fScanner.get_ch();
				if (ch == 's') {
					// most likely 1step
					fIsNumber = false;
					fKeyword = KW.ONE_STEP;
					fStringBuffer.append((char)ch);
					while ((ch = fScanner.get_ch()) != -1 && SVCharacter.isSVIdentifierPart(ch)) {
						fStringBuffer.append((char)ch);
					}
					fScanner.unget_ch(ch);
				} else {
					fScanner.unget_ch(ch);
				}
			}

			fImage = fStringBuffer.toString();
		} else if (ch == '(') {
			// Could be (, (*
			// Want to avoid (*) case
			ch2 = fScanner.get_ch();
			if (ch2 == '*') {
				int ch3 = fScanner.get_ch();
				if (ch3 != ')') {
					fOperator = OP.LPAREN_MUL;
					fScanner.unget_ch(ch3);
				} else {
					fOperator = OP.LPAREN;
					fScanner.unget_ch(ch3);
					fScanner.unget_ch(ch2);
				}
			} else {
				fOperator = OP.LPAREN;
				fScanner.unget_ch(ch2);
			}
		} else if (ch == '*') {
			// Could be *, **, *=, or *) or *>
			ch2 = fScanner.get_ch();

			if (ch2 == ')' && fInAttr) {
				fOperator = OP.MUL_RPAREN;
			} else if (ch2 == '*') {
				fOperator = OP.MUL2;
			} else if (ch2 == '=') {
				fOperator = OP.MUL_EQ;
			} else if (ch2 == '>') {
				fOperator = OP.MUL_GT;
			} else {
				fOperator = OP.MUL;
				fScanner.unget_ch(ch2);
			}
		} else if (SVCharacter.isSVIdentifierStart(ch)) {
			int last_ch = ch;
			boolean in_ref = false;
			// Identifier or keyword
			
			while ((ch = fScanner.get_ch()) != -1 && 
					(SVCharacter.isSVIdentifierPart(ch) ||
							(ch == '{' && last_ch == '$') ||
							(ch == '}' && in_ref))) {
				append_ch(ch);
				
				in_ref |= (last_ch == '$' && ch == '{');
				in_ref &= !(in_ref && ch == '}');
				
				last_ch = ch;
			}
			fScanner.unget_ch(ch);
			// Handle case where we received a single '$'
			if (fStringBuffer.length() == 1 && fStringBuffer.charAt(0) == '$') {
				fOperator = OP.DOLLAR;
			} else {
				fIsIdentifier = true;
			}
		} else if (ch == '\\') {
			// Escaped identifier
			fStringBuffer.setLength(0); // Clear '\' from buffer 
			while ((ch = fScanner.get_ch()) != -1 && !Character.isWhitespace(ch)) {
				append_ch(ch);
			}
			fScanner.unget_ch(ch);
			fIsIdentifier = true;
			escaped_id = true;
		} else /* if (fOperatorSet.contains(fStringBuffer.toString()) ||
				// Operators that can have up to three elements
				fSeqPrefixes[1].contains(fStringBuffer.toString()) ||
				fSeqPrefixes[2].contains(fStringBuffer.toString())) */ {
			operator();
		}
		
		if (fOperator == null && !fIsString && fStringBuffer.length() == 0) {
			fEOF = true;
			/*
			 * if (fEnableEOFException) { throw new EOFException(); }
			 */
			if (fDebugEn) {
				debug("EOF - " + SVDBLocation.toString(getStartLocation()));
			}
			if (fDebugEn) {
				fLog.debug("<-- next_token_int()");
			}
			return false;
		} else {
			fImage = fStringBuffer.toString();

			if (fIsIdentifier && !escaped_id) {
				Map<String, KW> kw = getKeywords(fContext);
				
				if ((fKeyword = kw.get(fImage)) != null) {
					fIsIdentifier = false;
				}				
			}
			fTokenConsumed = false;
			if (fDebugEn) {
				fLog.debug("next_token(): \"" + fImage + "\" @ " +
						SVDBLocation.unpackFileId(fStartLocation) + ":" +
						SVDBLocation.unpackLineno(fStartLocation));
				fLog.debug("<-- next_token_int()");
			}
			return true;
		}
	}
	
	private void append_ch(int ch) {
		fStringBuffer.append((char)ch);
		/*
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
		 */
	}
	
	private Map<String, KW> getKeywords(Context ctxt) {
		Map<String, KW> kw = null;
		switch (ctxt) {
			case Behavioral:
			case Default:
				kw = fDefaultKeywordSet;
				break;
			
			case Constraint:
				kw = fConstraintKeywordSet;
				break;
			
			case Expression:
				kw = fExprKeywordSet;
				break;
		}
		
		return kw;
	}
	
	private void operator() throws SVParseException {
		char st = fStringBuffer.charAt(0);
		fScanner.unget_ch(st);
		
		OP op = SVOperatorLexer.operator(fScanner);
		
//		fLog.debug("OP starting with " + st + ": " + op);
		
		if (op == null) {
			error("Problem with operator: " + fStringBuffer.toString());
		}
		
		fOperator = op;
//		fStringBuffer.setLength(0);
//		fStringBuffer.append(op.getImg());
		
		if (op == OP.HASH) {
			// May be a delay-control expression
			int ch;
			while ((ch = fScanner.get_ch()) != -1 && Character.isWhitespace(ch)) { }
			if (ch >= '0' && ch <= '9') {
				// delay-control
				fIsDelayControl = true;
			}
			fScanner.unget_ch(ch);
		}
	}

	private void operator_1() throws SVParseException {
		int ch;
		int op_idx=0; // index of the op prefix to check
		
		if (fDebugEn) {
			debug("operator: " + fStringBuffer.toString());
		}
		while (op_idx < 2) {
			// Add a character and check whether is a prefix for the next
			// sequence
			if ((ch = fScanner.get_ch()) != -1) {
				append_ch(ch);
				if (fDebugEn) {
					debug("  append: " + (char)ch + "  => " + fStringBuffer.toString());
				}
				if (!fSeqPrefixes[op_idx+1].contains(fStringBuffer.toString()) &&
						!fOperatorSet.contains(fStringBuffer.toString())) {
					// Doesn't match, so don't move forward
					fScanner.unget_ch(ch);
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
//		fIsOperator = true; // TODO:
		String val = fStringBuffer.toString();
		if (!fOperatorSet.contains(val)) {
			error("Problem with operator: " + fStringBuffer.toString());
		}
		
		if (val.equals("#")) {
			// May be a delay-control expression
			while ((ch = fScanner.get_ch()) != -1 && Character.isWhitespace(ch)) { }
			if (ch >= '0' && ch <= '9') {
				// delay-control
				fIsDelayControl = true;
			}
			fScanner.unget_ch(ch);
		}
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
			ch = fScanner.get_ch();
			append_ch(ch);
		}

		if (!isBaseChar(ch)) {
			error("Unknown base digit " + (char) ch);
		}
		base = Character.toLowerCase(ch);

		// Skip whitespace
		while ((ch = fScanner.get_ch()) != -1 && Character.isWhitespace(ch)) {
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
	private void readNumber(int ch, boolean is_delay_ctrl) throws SVParseException {

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
				int ch2 = fScanner.get_ch();
				if (SVCharacter.isSVIdentifierPart(ch2)) {
					fScanner.unget_ch(ch2);
				} else {
					append_ch(ch);
					ch = ch2;
				}
			} else {
				ch = readTimeUnit(ch);
			}
		} else if (ch == '.' || ch == 'e' || ch == 'E') {
			ch = readRealNumber(ch);
		} else if (is_delay_ctrl) {
			// do nothing. We do not want to accidentally 
			// continue across a number boundary
		} else {
			boolean found_ws = false;
			while (ch != -1 && Character.isWhitespace(ch)) {
				ch = fScanner.get_ch();
				found_ws = true;
			}

			if (ch == '\'') {
				int ch2 = fScanner.get_ch();
				
				if (ch2 == 's' || ch == 'S') {
					append_ch(ch);
					
					append_ch(ch2);
					ch2 = fScanner.get_ch();
					if (!isBaseChar(ch2)) {
						error("Unknown base digit " + (char)ch2);
					}

					ch = readBasedNumber(ch2);
				} else {
					if (isBaseChar(ch2)) {
						append_ch(ch);
						ch = readBasedNumber(ch2);
					} else {
						// Likely an integer cast
						fScanner.unget_ch(ch2);
					}
				}
			} else {
				// Really just a decimal number. Insert the
				// whitespace
				if (found_ws) {
					fScanner.unget_ch(ch);
					ch = ' ';
				}
			}
		}

		fScanner.unget_ch(ch);
	}

	private static boolean isDecDigit(int ch) {
		return (ch >= '0' && ch <= '9');
	}

	private int readDecNumber(int ch) throws SVParseException {
		while (ch >= '0' && ch <= '9' || ch == '_' || 
				ch == 'z' || ch == 'Z' || ch == 'x' || ch == 'X') {
			append_ch(ch);
			ch = fScanner.get_ch();
		}
		return ch;
	}

	// enter on post-'.'
	private int readRealNumber(int ch) throws SVParseException {
		if (ch == '.') {
			append_ch(ch);
			ch = readDecNumber(fScanner.get_ch());
		}

		if (ch == 'e' || ch == 'E') {
			append_ch(ch);
			ch = fScanner.get_ch();
			if (ch == '-' || ch == '+') {
				append_ch(ch);
				ch = fScanner.get_ch();
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
			ch = fScanner.get_ch();

			if (ch != 's') {
				error("Malformed time unit n" + (char) ch);
			}
			append_ch(ch);
		}
		
		fIsTime = true;

		return fScanner.get_ch();
	}

	private int readHexNumber(int ch) throws SVParseException {
		while (ch != -1
				&& ((ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f')
						|| (ch >= 'A' && ch <= 'F') || ch == '_' || ch == 'x'
						|| ch == 'X' || ch == 'z' || ch == 'Z' || ch == '?')) {
			append_ch(ch);
			ch = fScanner.get_ch();
		}

		return ch;
	}

	private int readOctNumber(int ch) throws SVParseException {
		while (ch != -1
				&& ((ch >= '0' && ch <= '7') || ch == '_' || ch == 'x'
						|| ch == 'X' || ch == 'z' || ch == 'Z' || ch == '?')) {
			append_ch(ch);
			ch = fScanner.get_ch();
		}

		return ch;
	}

	private int readBinNumber(int ch) throws SVParseException {
		while (ch != -1
				&& (ch == '0' || ch == '1' || ch == '_' || ch == 'x'
						|| ch == 'X' || ch == 'z' || ch == 'Z' || ch == '?')) {
			append_ch(ch);
			ch = fScanner.get_ch();
		}

		return ch;
	}

	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}

	private void error(String msg) throws SVParseException {
		setInAttr(false);
		fParser.error(msg);
	}
}

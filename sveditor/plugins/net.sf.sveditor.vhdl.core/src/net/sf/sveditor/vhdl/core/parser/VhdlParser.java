// $ANTLR 2.7.7 (2006-11-01): "net.sf.sveditor.vhdl.core/src/net/sf/sveditor/vhdl/core/parser/vhdl.g" -> "VhdlParser.java"$

package net.sf.sveditor.vhdl.core.parser;

import antlr.TokenBuffer;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.ANTLRException;
import antlr.LLkParser;
import antlr.Token;
import antlr.TokenStream;
import antlr.RecognitionException;
import antlr.NoViableAltException;
import antlr.MismatchedTokenException;
import antlr.SemanticException;
import antlr.ParserSharedInputState;
import antlr.collections.impl.BitSet;

public class VhdlParser extends antlr.LLkParser       implements VhdlParserTokenTypes
 {

	/**
	 *	Track module declarations and instances.
	 */
	public static Tracker	stTracker = new Tracker();

	/**
	 *	A convenience for building Token
	 */
	private static class BldToken extends antlr.CommonToken {
		private BldToken(Token orig, String news) {
			super(orig.getType(), news);
			setFilename(orig.getFilename());
			setLine(orig.getLine());
		}
	}

protected VhdlParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public VhdlParser(TokenBuffer tokenBuf) {
  this(tokenBuf,2);
}

protected VhdlParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public VhdlParser(TokenStream lexer) {
  this(lexer,2);
}

public VhdlParser(ParserSharedInputState state) {
  super(state,2);
  tokenNames = _tokenNames;
}

	public final void abstract_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case DECIMAL_LITERAL:
			{
				decimal_literal();
				break;
			}
			case BASED_LITERAL:
			{
				based_literal();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void decimal_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(DECIMAL_LITERAL);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void based_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(BASED_LITERAL);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void access_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ACCESS);
			subtype_indication();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subtype_indication() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			name();
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				break;
			}
			case EOF:
			case K_OPEN:
			case LPAREN:
			case RPAREN:
			case PLUS:
			case MINUS:
			case AND:
			case COMMA:
			case K_IS:
			case SEMI:
			case K_REPORT:
			case K_SEVERITY:
			case EQGRT:
			case K_FOR:
			case K_WHEN:
			case BAR:
			case LSTEQ:
			case K_ELSE:
			case COLONEQ:
			case K_INERTIAL:
			case K_TO:
			case K_DOWNTO:
			case K_AFTER:
			case K_UNITS:
			case K_AND:
			case K_OR:
			case K_XOR:
			case K_NAND:
			case K_NOR:
			case K_XNOR:
			case STAR2:
			case K_GENERATE:
			case K_THEN:
			case K_RANGE:
			case K_BUS:
			case K_LOOP:
			case STAR:
			case SLASH:
			case K_MOD:
			case K_REM:
			case EQ:
			case SLASHEQ:
			case LST:
			case GRT:
			case GRTEQ:
			case K_SELECT:
			case K_SLL:
			case K_SRL:
			case K_SLA:
			case K_SRA:
			case K_ROL:
			case K_ROR:
			case K_REGISTER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case LPAREN:
			case K_RANGE:
			{
				constraint();
				break;
			}
			case EOF:
			case K_OPEN:
			case RPAREN:
			case PLUS:
			case MINUS:
			case AND:
			case COMMA:
			case K_IS:
			case SEMI:
			case K_REPORT:
			case K_SEVERITY:
			case EQGRT:
			case K_FOR:
			case K_WHEN:
			case BAR:
			case LSTEQ:
			case K_ELSE:
			case COLONEQ:
			case K_INERTIAL:
			case K_TO:
			case K_DOWNTO:
			case K_AFTER:
			case K_UNITS:
			case K_AND:
			case K_OR:
			case K_XOR:
			case K_NAND:
			case K_NOR:
			case K_XNOR:
			case STAR2:
			case K_GENERATE:
			case K_THEN:
			case K_BUS:
			case K_LOOP:
			case STAR:
			case SLASH:
			case K_MOD:
			case K_REM:
			case EQ:
			case SLASHEQ:
			case LST:
			case GRT:
			case GRTEQ:
			case K_SELECT:
			case K_SLL:
			case K_SRL:
			case K_SLA:
			case K_SRA:
			case K_ROL:
			case K_ROR:
			case K_REGISTER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void actual_designator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			case PLUS:
			case MINUS:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case K_ABS:
			case K_NOT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			{
				expression();
				break;
			}
			case K_OPEN:
			{
				match(K_OPEN);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void expression() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			relation();
			{
			_loop245:
			do {
				if (((LA(1) >= K_AND && LA(1) <= K_XNOR))) {
					logical_op();
					relation();
				}
				else {
					break _loop245;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void actual_parameter_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			association_list();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void association_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			association_element();
			{
			_loop43:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					association_element();
				}
				else {
					break _loop43;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void actual_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched7 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_6.member(LA(2))))) {
				int _m7 = mark();
				synPredMatched7 = true;
				inputState.guessing++;
				try {
					{
					name();
					match(LPAREN);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched7 = false;
				}
				rewind(_m7);
inputState.guessing--;
			}
			if ( synPredMatched7 ) {
				name();
				match(LPAREN);
				actual_designator();
				match(RPAREN);
			}
			else if ((_tokenSet_7.member(LA(1))) && (_tokenSet_8.member(LA(2)))) {
				actual_designator();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Token  name() throws RecognitionException, TokenStreamException {
		Token tok;
		
			StringBuilder smplName = null;
			Token first = null;
			tok = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				tok=simple_name();
				if ( inputState.guessing==0 ) {
					smplName = new StringBuilder(tok.getText()); first=tok;
				}
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			_loop362:
			do {
				if ((_tokenSet_6.member(LA(1))) && (_tokenSet_9.member(LA(2)))) {
					{
					switch ( LA(1)) {
					case DOT:
					{
						match(DOT);
						tok=suffix();
						if ( inputState.guessing==0 ) {
								if ((tok != null) && (null != smplName)) {
													smplName.append('.').append(tok.getText());
												}
											
						}
						break;
					}
					case TIC:
					{
						match(TIC);
						aggregate();
						break;
					}
					case TIC_SIMPLE_NAME:
					case LBRACK:
					{
						{
						switch ( LA(1)) {
						case LBRACK:
						{
							signature();
							break;
						}
						case TIC_SIMPLE_NAME:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						tic_attribute_designator();
						break;
					}
					default:
						boolean synPredMatched357 = false;
						if (((LA(1)==LPAREN) && (_tokenSet_10.member(LA(2))))) {
							int _m357 = mark();
							synPredMatched357 = true;
							inputState.guessing++;
							try {
								{
								match(LPAREN);
								expression();
								{
								_loop356:
								do {
									if ((LA(1)==COMMA)) {
										match(COMMA);
										expression();
									}
									else {
										break _loop356;
									}
									
								} while (true);
								}
								match(RPAREN);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched357 = false;
							}
							rewind(_m357);
inputState.guessing--;
						}
						if ( synPredMatched357 ) {
							match(LPAREN);
							expression();
							{
							_loop359:
							do {
								if ((LA(1)==COMMA)) {
									match(COMMA);
									expression();
								}
								else {
									break _loop359;
								}
								
							} while (true);
							}
							match(RPAREN);
						}
						else {
							boolean synPredMatched361 = false;
							if (((LA(1)==LPAREN) && (_tokenSet_7.member(LA(2))))) {
								int _m361 = mark();
								synPredMatched361 = true;
								inputState.guessing++;
								try {
									{
									match(LPAREN);
									actual_parameter_part();
									match(RPAREN);
									}
								}
								catch (RecognitionException pe) {
									synPredMatched361 = false;
								}
								rewind(_m361);
inputState.guessing--;
							}
							if ( synPredMatched361 ) {
								match(LPAREN);
								actual_parameter_part();
								match(RPAREN);
							}
							else if ((LA(1)==LPAREN) && (_tokenSet_10.member(LA(2)))) {
								match(LPAREN);
								discrete_range();
								match(RPAREN);
							}
						else {
							throw new NoViableAltException(LT(1), getFilename());
						}
						}}
						}
					}
					else {
						break _loop362;
					}
					
				} while (true);
				}
				if ( inputState.guessing==0 ) {
					
							if (null != first) {
								tok = new BldToken(first, smplName.toString());
							}
						
				}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_11);
				} else {
				  throw ex;
				}
			}
			return tok;
		}
		
	public final void adding_operator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case PLUS:
			{
				match(PLUS);
				break;
			}
			case MINUS:
			{
				match(MINUS);
				break;
			}
			case AND:
			{
				match(AND);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_12);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void aggregate() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(LPAREN);
			element_association();
			{
			_loop11:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					element_association();
				}
				else {
					break _loop11;
				}
				
			} while (true);
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void element_association() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			boolean synPredMatched192 = false;
			if (((_tokenSet_14.member(LA(1))) && (_tokenSet_15.member(LA(2))))) {
				int _m192 = mark();
				synPredMatched192 = true;
				inputState.guessing++;
				try {
					{
					choices();
					match(EQGRT);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched192 = false;
				}
				rewind(_m192);
inputState.guessing--;
			}
			if ( synPredMatched192 ) {
				choices();
				match(EQGRT);
			}
			else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_8.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			expression();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void alias_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ALIAS);
			alias_designator();
			{
			switch ( LA(1)) {
			case COLON:
			{
				match(COLON);
				subtype_indication();
				break;
			}
			case K_IS:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_IS);
			name();
			{
			switch ( LA(1)) {
			case LBRACK:
			{
				signature();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void alias_designator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				identifier();
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_17);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void signature() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(LBRACK);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				{
				_loop548:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						name();
					}
					else {
						break _loop548;
					}
					
				} while (true);
				}
				break;
			}
			case K_RETURN:
			case RBRACK:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_RETURN:
			{
				match(K_RETURN);
				name();
				break;
			}
			case RBRACK:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RBRACK);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_18);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Token  identifier() throws RecognitionException, TokenStreamException {
		Token tok;
		
		Token  id = null;
		Token  id2 = null;
		tok=null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			{
				id = LT(1);
				match(BASIC_IDENTIFIER);
				if ( inputState.guessing==0 ) {
					tok=id;
				}
				break;
			}
			case EXTENDED_IDENTIFIER:
			{
				id2 = LT(1);
				match(EXTENDED_IDENTIFIER);
				if ( inputState.guessing==0 ) {
					tok=id2;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_19);
			} else {
			  throw ex;
			}
		}
		return tok;
	}
	
	public final void character_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(CHARACTER_LITERAL);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void operator_symbol() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			string_literal();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void allocator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_NEW);
			{
			boolean synPredMatched19 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_20.member(LA(2))))) {
				int _m19 = mark();
				synPredMatched19 = true;
				inputState.guessing++;
				try {
					{
					subtype_indication();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched19 = false;
				}
				rewind(_m19);
inputState.guessing--;
			}
			if ( synPredMatched19 ) {
				subtype_indication();
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_6.member(LA(2)))) {
				qualified_expression();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void qualified_expression() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			name();
			match(TIC);
			{
			boolean synPredMatched463 = false;
			if (((LA(1)==LPAREN) && (_tokenSet_14.member(LA(2))))) {
				int _m463 = mark();
				synPredMatched463 = true;
				inputState.guessing++;
				try {
					{
					aggregate();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched463 = false;
				}
				rewind(_m463);
inputState.guessing--;
			}
			if ( synPredMatched463 ) {
				aggregate();
			}
			else if ((LA(1)==LPAREN) && (_tokenSet_10.member(LA(2)))) {
				match(LPAREN);
				expression();
				match(RPAREN);
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void architecture_body() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ARCHITECTURE);
			identifier();
			match(K_OF);
			name();
			match(K_IS);
			architecture_declarative_part();
			match(K_BEGIN);
			architecture_statement_part();
			match(K_END);
			{
			switch ( LA(1)) {
			case K_ARCHITECTURE:
			{
				match(K_ARCHITECTURE);
				break;
			}
			case SEMI:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void architecture_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop25:
			do {
				if ((_tokenSet_22.member(LA(1)))) {
					block_declarative_item();
				}
				else {
					break _loop25;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void architecture_statement_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop28:
			do {
				if ((_tokenSet_24.member(LA(1)))) {
					concurrent_statement();
				}
				else {
					break _loop28;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Token  simple_name() throws RecognitionException, TokenStreamException {
		Token tok;
		
		tok=null;
		
		try {      // for error handling
			tok=identifier();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_26);
			} else {
			  throw ex;
			}
		}
		return tok;
	}
	
	public final void block_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_COMPONENT:
			{
				component_declaration();
				break;
			}
			case K_FOR:
			{
				configuration_specification();
				break;
			}
			case K_DISCONNECT:
			{
				disconnection_specification();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
				boolean synPredMatched62 = false;
				if (((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2))))) {
					int _m62 = mark();
					synPredMatched62 = true;
					inputState.guessing++;
					try {
						{
						subprogram_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched62 = false;
					}
					rewind(_m62);
inputState.guessing--;
				}
				if ( synPredMatched62 ) {
					subprogram_declaration();
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
				}
				else {
					boolean synPredMatched64 = false;
					if (((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m64 = mark();
						synPredMatched64 = true;
						inputState.guessing++;
						try {
							{
							attribute_specification();
							}
						}
						catch (RecognitionException pe) {
							synPredMatched64 = false;
						}
						rewind(_m64);
inputState.guessing--;
					}
					if ( synPredMatched64 ) {
						attribute_specification();
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
					}
					else {
						boolean synPredMatched66 = false;
						if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
							int _m66 = mark();
							synPredMatched66 = true;
							inputState.guessing++;
							try {
								{
								match(K_GROUP);
								identifier();
								match(COLON);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched66 = false;
							}
							rewind(_m66);
inputState.guessing--;
						}
						if ( synPredMatched66 ) {
							group_declaration();
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
						}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					}}}
				}
				catch (RecognitionException ex) {
					if (inputState.guessing==0) {
						reportError(ex);
						recover(ex,_tokenSet_29);
					} else {
					  throw ex;
					}
				}
			}
			
	public final void concurrent_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched129 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON))) {
				int _m129 = mark();
				synPredMatched129 = true;
				inputState.guessing++;
				try {
					{
					block_statement();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched129 = false;
				}
				rewind(_m129);
inputState.guessing--;
			}
			if ( synPredMatched129 ) {
				block_statement();
			}
			else {
				boolean synPredMatched131 = false;
				if (((_tokenSet_30.member(LA(1))) && (_tokenSet_31.member(LA(2))))) {
					int _m131 = mark();
					synPredMatched131 = true;
					inputState.guessing++;
					try {
						{
						process_statement();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched131 = false;
					}
					rewind(_m131);
inputState.guessing--;
				}
				if ( synPredMatched131 ) {
					process_statement();
				}
				else {
					boolean synPredMatched133 = false;
					if (((_tokenSet_32.member(LA(1))) && (_tokenSet_33.member(LA(2))))) {
						int _m133 = mark();
						synPredMatched133 = true;
						inputState.guessing++;
						try {
							{
							concurrent_procedure_call_statement();
							}
						}
						catch (RecognitionException pe) {
							synPredMatched133 = false;
						}
						rewind(_m133);
inputState.guessing--;
					}
					if ( synPredMatched133 ) {
						concurrent_procedure_call_statement();
					}
					else {
						boolean synPredMatched135 = false;
						if (((_tokenSet_34.member(LA(1))) && (_tokenSet_35.member(LA(2))))) {
							int _m135 = mark();
							synPredMatched135 = true;
							inputState.guessing++;
							try {
								{
								concurrent_assertion_statement();
								}
							}
							catch (RecognitionException pe) {
								synPredMatched135 = false;
							}
							rewind(_m135);
inputState.guessing--;
						}
						if ( synPredMatched135 ) {
							concurrent_assertion_statement();
						}
						else {
							boolean synPredMatched137 = false;
							if (((_tokenSet_36.member(LA(1))) && (_tokenSet_37.member(LA(2))))) {
								int _m137 = mark();
								synPredMatched137 = true;
								inputState.guessing++;
								try {
									{
									concurrent_signal_assignment_statement();
									}
								}
								catch (RecognitionException pe) {
									synPredMatched137 = false;
								}
								rewind(_m137);
inputState.guessing--;
							}
							if ( synPredMatched137 ) {
								concurrent_signal_assignment_statement();
							}
							else {
								boolean synPredMatched139 = false;
								if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON))) {
									int _m139 = mark();
									synPredMatched139 = true;
									inputState.guessing++;
									try {
										{
										component_instantiation_statement();
										}
									}
									catch (RecognitionException pe) {
										synPredMatched139 = false;
									}
									rewind(_m139);
inputState.guessing--;
								}
								if ( synPredMatched139 ) {
									component_instantiation_statement();
								}
								else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
									generate_statement();
								}
								else {
									throw new NoViableAltException(LT(1), getFilename());
								}
								}}}}}
							}
							catch (RecognitionException ex) {
								if (inputState.guessing==0) {
									reportError(ex);
									recover(ex,_tokenSet_38);
								} else {
								  throw ex;
								}
							}
						}
						
	public final void array_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched31 = false;
			if (((LA(1)==K_ARRAY) && (LA(2)==LPAREN))) {
				int _m31 = mark();
				synPredMatched31 = true;
				inputState.guessing++;
				try {
					{
					unconstrained_array_definition();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched31 = false;
				}
				rewind(_m31);
inputState.guessing--;
			}
			if ( synPredMatched31 ) {
				unconstrained_array_definition();
			}
			else if ((LA(1)==K_ARRAY) && (LA(2)==LPAREN)) {
				constrained_array_definition();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void unconstrained_array_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ARRAY);
			match(LPAREN);
			index_subtype_definition();
			{
			_loop594:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					index_subtype_definition();
				}
				else {
					break _loop594;
				}
				
			} while (true);
			}
			match(RPAREN);
			match(K_OF);
			subtype_indication();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void constrained_array_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ARRAY);
			index_constraint();
			match(K_OF);
			subtype_indication();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void assertion() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ASSERT);
			condition();
			{
			switch ( LA(1)) {
			case K_REPORT:
			{
				match(K_REPORT);
				expression();
				break;
			}
			case SEMI:
			case K_SEVERITY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_SEVERITY:
			{
				match(K_SEVERITY);
				expression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void condition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			expression();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_39);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void assertion_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_ASSERT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			assertion();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void label_colon() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			label();
			match(COLON);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_41);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void association_element() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			boolean synPredMatched40 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_42.member(LA(2))))) {
				int _m40 = mark();
				synPredMatched40 = true;
				inputState.guessing++;
				try {
					{
					formal_part();
					match(EQGRT);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched40 = false;
				}
				rewind(_m40);
inputState.guessing--;
			}
			if ( synPredMatched40 ) {
				formal_part();
				match(EQGRT);
			}
			else if ((_tokenSet_7.member(LA(1))) && (_tokenSet_8.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			actual_part();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void formal_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			name();
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				name();
				match(RPAREN);
				break;
			}
			case EQGRT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_43);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void attribute_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ATTRIBUTE);
			identifier();
			match(COLON);
			name();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void attribute_designator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			simple_name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_44);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void tic_attribute_designator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(TIC_SIMPLE_NAME);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void attribute_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ATTRIBUTE);
			attribute_designator();
			match(K_OF);
			entity_specification();
			match(K_IS);
			expression();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_45);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			entity_name_list();
			match(COLON);
			entity_class();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_46);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void base_unit_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			identifier();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_47);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void binding_indication() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_USE:
			{
				match(K_USE);
				entity_aspect();
				break;
			}
			case SEMI:
			case K_GENERIC:
			case K_PORT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_map_aspect();
				break;
			}
			case SEMI:
			case K_PORT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_PORT:
			{
				port_map_aspect();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_aspect() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ENTITY:
			{
				match(K_ENTITY);
				name();
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					match(LPAREN);
					identifier();
					match(RPAREN);
					break;
				}
				case SEMI:
				case K_GENERIC:
				case K_PORT:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case K_CONFIGURATION:
			{
				match(K_CONFIGURATION);
				name();
				break;
			}
			case K_OPEN:
			{
				match(K_OPEN);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_48);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void generic_map_aspect() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_GENERIC);
			match(K_MAP);
			match(LPAREN);
			association_list();
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_49);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void port_map_aspect() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_PORT);
			match(K_MAP);
			match(LPAREN);
			association_list();
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void bit_string_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(BIT_STRING_LITERAL);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void block_configuration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_FOR);
			block_specification();
			{
			_loop57:
			do {
				if ((LA(1)==K_USE)) {
					use_clause();
				}
				else {
					break _loop57;
				}
				
			} while (true);
			}
			{
			_loop59:
			do {
				if ((LA(1)==K_FOR)) {
					configuration_item();
				}
				else {
					break _loop59;
				}
				
			} while (true);
			}
			match(K_END);
			match(K_FOR);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_50);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void block_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched77 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==LPAREN))) {
				int _m77 = mark();
				synPredMatched77 = true;
				inputState.guessing++;
				try {
					{
					label();
					match(LPAREN);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched77 = false;
				}
				rewind(_m77);
inputState.guessing--;
			}
			if ( synPredMatched77 ) {
				label();
				match(LPAREN);
				index_specification();
				match(RPAREN);
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_51.member(LA(2)))) {
				name();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_52);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void use_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_USE);
			name();
			{
			_loop597:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					name();
				}
				else {
					break _loop597;
				}
				
			} while (true);
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_53);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void configuration_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched161 = false;
			if (((LA(1)==K_FOR) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER||LA(2)==STRING_LITERAL))) {
				int _m161 = mark();
				synPredMatched161 = true;
				inputState.guessing++;
				try {
					{
					block_configuration();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched161 = false;
				}
				rewind(_m161);
inputState.guessing--;
			}
			if ( synPredMatched161 ) {
				block_configuration();
			}
			else if ((LA(1)==K_FOR) && (_tokenSet_54.member(LA(2)))) {
				component_configuration();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_50);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subprogram_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			subprogram_specification();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subprogram_body() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			subprogram_specification();
			match(K_IS);
			subprogram_declarative_part();
			match(K_BEGIN);
			subprogram_statement_part();
			match(K_END);
			{
			switch ( LA(1)) {
			case K_PROCEDURE:
			case K_FUNCTION:
			{
				subprogram_kind();
				break;
			}
			case SEMI:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				designator();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_45);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void type_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched590 = false;
			if (((LA(1)==K_TYPE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
				int _m590 = mark();
				synPredMatched590 = true;
				inputState.guessing++;
				try {
					{
					full_type_declaration();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched590 = false;
				}
				rewind(_m590);
inputState.guessing--;
			}
			if ( synPredMatched590 ) {
				full_type_declaration();
			}
			else if ((LA(1)==K_TYPE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
				incomplete_type_declaration();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subtype_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_SUBTYPE);
			identifier();
			match(K_IS);
			subtype_indication();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void constant_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_CONSTANT);
			identifier_list();
			match(COLON);
			subtype_indication();
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				match(COLONEQ);
				expression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void signal_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_SIGNAL);
			identifier_list();
			match(COLON);
			subtype_indication();
			{
			switch ( LA(1)) {
			case K_BUS:
			case K_REGISTER:
			{
				signal_kind();
				break;
			}
			case SEMI:
			case COLONEQ:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				match(COLONEQ);
				expression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void variable_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_SHARED:
			{
				match(K_SHARED);
				break;
			}
			case K_VARIABLE:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_VARIABLE);
			identifier_list();
			match(COLON);
			subtype_indication();
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				match(COLONEQ);
				expression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void file_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_FILE);
			identifier_list();
			match(COLON);
			subtype_indication();
			{
			switch ( LA(1)) {
			case K_OPEN:
			case K_IS:
			{
				file_open_information();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void component_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_COMPONENT);
			identifier();
			{
			switch ( LA(1)) {
			case K_IS:
			{
				match(K_IS);
				break;
			}
			case K_END:
			case K_GENERIC:
			case K_PORT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_clause();
				break;
			}
			case K_END:
			case K_PORT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_PORT:
			{
				port_clause();
				break;
			}
			case K_END:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_END);
			match(K_COMPONENT);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void configuration_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_FOR);
			component_specification();
			binding_indication();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_29);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void disconnection_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_DISCONNECT);
			guarded_signal_specification();
			match(K_AFTER);
			expression();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_45);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void group_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_GROUP);
			identifier();
			match(COLON);
			name();
			match(LPAREN);
			group_constituent_list();
			match(RPAREN);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void group_template_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_GROUP);
			identifier();
			match(K_IS);
			match(LPAREN);
			entity_class_entry_list();
			match(RPAREN);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void block_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop69:
			do {
				if ((_tokenSet_22.member(LA(1)))) {
					block_declarative_item();
				}
				else {
					break _loop69;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void block_header() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_clause();
				{
				switch ( LA(1)) {
				case K_GENERIC:
				{
					generic_map_aspect();
					match(SEMI);
					break;
				}
				case K_ALIAS:
				case K_BEGIN:
				case K_ATTRIBUTE:
				case K_USE:
				case K_FOR:
				case K_GROUP:
				case K_COMPONENT:
				case K_CONSTANT:
				case K_DISCONNECT:
				case K_PROCEDURE:
				case K_TYPE:
				case K_SIGNAL:
				case K_FUNCTION:
				case K_SUBTYPE:
				case K_VARIABLE:
				case K_FILE:
				case K_PORT:
				case K_PURE:
				case K_IMPURE:
				case K_SHARED:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case K_ALIAS:
			case K_BEGIN:
			case K_ATTRIBUTE:
			case K_USE:
			case K_FOR:
			case K_GROUP:
			case K_COMPONENT:
			case K_CONSTANT:
			case K_DISCONNECT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_SIGNAL:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_PORT:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_PORT:
			{
				port_clause();
				{
				switch ( LA(1)) {
				case K_PORT:
				{
					port_map_aspect();
					match(SEMI);
					break;
				}
				case K_ALIAS:
				case K_BEGIN:
				case K_ATTRIBUTE:
				case K_USE:
				case K_FOR:
				case K_GROUP:
				case K_COMPONENT:
				case K_CONSTANT:
				case K_DISCONNECT:
				case K_PROCEDURE:
				case K_TYPE:
				case K_SIGNAL:
				case K_FUNCTION:
				case K_SUBTYPE:
				case K_VARIABLE:
				case K_FILE:
				case K_PURE:
				case K_IMPURE:
				case K_SHARED:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case K_ALIAS:
			case K_BEGIN:
			case K_ATTRIBUTE:
			case K_USE:
			case K_FOR:
			case K_GROUP:
			case K_COMPONENT:
			case K_CONSTANT:
			case K_DISCONNECT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_SIGNAL:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_29);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void generic_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_GENERIC);
			match(LPAREN);
			generic_list();
			match(RPAREN);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_55);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void port_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_PORT);
			match(LPAREN);
			port_list();
			match(RPAREN);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_56);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Token  label() throws RecognitionException, TokenStreamException {
		Token tok;
		
		tok=null;
		
		try {      // for error handling
			tok=identifier();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_57);
			} else {
			  throw ex;
			}
		}
		return tok;
	}
	
	public final void index_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched296 = false;
			if (((_tokenSet_10.member(LA(1))) && (_tokenSet_58.member(LA(2))))) {
				int _m296 = mark();
				synPredMatched296 = true;
				inputState.guessing++;
				try {
					{
					discrete_range();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched296 = false;
				}
				rewind(_m296);
inputState.guessing--;
			}
			if ( synPredMatched296 ) {
				discrete_range();
			}
			else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_59.member(LA(2)))) {
				expression();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void block_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			label();
			match(COLON);
			match(K_BLOCK);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				expression();
				match(RPAREN);
				break;
			}
			case K_ALIAS:
			case K_IS:
			case K_BEGIN:
			case K_ATTRIBUTE:
			case K_USE:
			case K_FOR:
			case K_GROUP:
			case K_COMPONENT:
			case K_CONSTANT:
			case K_DISCONNECT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_SIGNAL:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_GENERIC:
			case K_PORT:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_IS:
			{
				match(K_IS);
				break;
			}
			case K_ALIAS:
			case K_BEGIN:
			case K_ATTRIBUTE:
			case K_USE:
			case K_FOR:
			case K_GROUP:
			case K_COMPONENT:
			case K_CONSTANT:
			case K_DISCONNECT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_SIGNAL:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_GENERIC:
			case K_PORT:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			block_header();
			block_declarative_part();
			match(K_BEGIN);
			block_statement_part();
			match(K_END);
			match(K_BLOCK);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void block_statement_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop84:
			do {
				if ((_tokenSet_24.member(LA(1)))) {
					concurrent_statement();
				}
				else {
					break _loop84;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void case_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_CASE:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_CASE);
			expression();
			match(K_IS);
			{
			int _cnt88=0;
			_loop88:
			do {
				if ((LA(1)==K_WHEN)) {
					case_statement_alternative();
				}
				else {
					if ( _cnt88>=1 ) { break _loop88; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt88++;
			} while (true);
			}
			match(K_END);
			match(K_CASE);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void case_statement_alternative() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_WHEN);
			choices();
			match(EQGRT);
			sequence_of_statements();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_60);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void choices() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			choice();
			{
			_loop99:
			do {
				if ((LA(1)==BAR)) {
					match(BAR);
					choice();
				}
				else {
					break _loop99;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_61);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void sequence_of_statements() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop496:
			do {
				if ((_tokenSet_62.member(LA(1)))) {
					sequential_statement();
				}
				else {
					break _loop496;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_63);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void choice() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched94 = false;
			if (((_tokenSet_10.member(LA(1))) && (_tokenSet_64.member(LA(2))))) {
				int _m94 = mark();
				synPredMatched94 = true;
				inputState.guessing++;
				try {
					{
					simple_expression();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched94 = false;
				}
				rewind(_m94);
inputState.guessing--;
			}
			if ( synPredMatched94 ) {
				simple_expression();
			}
			else {
				boolean synPredMatched96 = false;
				if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_65.member(LA(2))))) {
					int _m96 = mark();
					synPredMatched96 = true;
					inputState.guessing++;
					try {
						{
						simple_name();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched96 = false;
					}
					rewind(_m96);
inputState.guessing--;
				}
				if ( synPredMatched96 ) {
					simple_name();
				}
				else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_66.member(LA(2)))) {
					discrete_range();
				}
				else if ((LA(1)==K_OTHERS)) {
					match(K_OTHERS);
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_65);
				} else {
				  throw ex;
				}
			}
		}
		
	public final void simple_expression() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case PLUS:
			case MINUS:
			{
				sign();
				break;
			}
			case LPAREN:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case K_ABS:
			case K_NOT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			term();
			{
			_loop553:
			do {
				if (((LA(1) >= PLUS && LA(1) <= AND)) && (_tokenSet_12.member(LA(2)))) {
					adding_operator();
					term();
				}
				else {
					break _loop553;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void discrete_range() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched188 = false;
			if (((_tokenSet_10.member(LA(1))) && (_tokenSet_67.member(LA(2))))) {
				int _m188 = mark();
				synPredMatched188 = true;
				inputState.guessing++;
				try {
					{
					range();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched188 = false;
				}
				rewind(_m188);
inputState.guessing--;
			}
			if ( synPredMatched188 ) {
				range();
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_68.member(LA(2)))) {
				subtype_indication();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_69);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void component_configuration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_FOR);
			component_specification();
			{
			switch ( LA(1)) {
			case SEMI:
			case K_USE:
			case K_GENERIC:
			case K_PORT:
			{
				binding_indication();
				match(SEMI);
				break;
			}
			case K_END:
			case K_FOR:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_FOR:
			{
				block_configuration();
				break;
			}
			case K_END:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_END);
			match(K_FOR);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_50);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void component_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			instantiation_list();
			match(COLON);
			name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_70);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void component_instantiation_statement() throws RecognitionException, TokenStreamException {
		
		Token instNm = null, refNm = null;
		
		try {      // for error handling
			instNm=label();
			match(COLON);
			refNm=instantiated_unit();
			if ( inputState.guessing==0 ) {
				stTracker.addInstance(refNm, instNm);
			}
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_map_aspect();
				break;
			}
			case SEMI:
			case K_PORT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_PORT:
			{
				port_map_aspect();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Token  instantiated_unit() throws RecognitionException, TokenStreamException {
		Token tok;
		
		tok=null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_COMPONENT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				{
				switch ( LA(1)) {
				case K_COMPONENT:
				{
					match(K_COMPONENT);
					break;
				}
				case BASIC_IDENTIFIER:
				case EXTENDED_IDENTIFIER:
				case STRING_LITERAL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				tok=name();
				break;
			}
			case K_ENTITY:
			{
				match(K_ENTITY);
				tok=name();
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					match(LPAREN);
					identifier();
					match(RPAREN);
					break;
				}
				case SEMI:
				case K_GENERIC:
				case K_PORT:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case K_CONFIGURATION:
			{
				match(K_CONFIGURATION);
				name();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_48);
			} else {
			  throw ex;
			}
		}
		return tok;
	}
	
	public final void instantiation_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				{
				_loop303:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						label();
					}
					else {
						break _loop303;
					}
					
				} while (true);
				}
				break;
			}
			case K_OTHERS:
			{
				match(K_OTHERS);
				break;
			}
			case K_ALL:
			{
				match(K_ALL);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_71);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void composite_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ARRAY:
			{
				array_type_definition();
				break;
			}
			case K_RECORD:
			{
				record_type_definition();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void record_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_RECORD);
			{
			int _cnt470=0;
			_loop470:
			do {
				if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER)) {
					element_declaration();
				}
				else {
					if ( _cnt470>=1 ) { break _loop470; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt470++;
			} while (true);
			}
			match(K_END);
			match(K_RECORD);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void concurrent_assertion_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_ASSERT:
			case K_POSTPONED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_POSTPONED:
			{
				match(K_POSTPONED);
				break;
			}
			case K_ASSERT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			assertion();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void concurrent_procedure_call_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched118 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON))) {
				int _m118 = mark();
				synPredMatched118 = true;
				inputState.guessing++;
				try {
					{
					label_colon();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched118 = false;
				}
				rewind(_m118);
inputState.guessing--;
			}
			if ( synPredMatched118 ) {
				label_colon();
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					match(K_POSTPONED);
					break;
				}
				case BASIC_IDENTIFIER:
				case EXTENDED_IDENTIFIER:
				case STRING_LITERAL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				procedure_call();
				match(SEMI);
			}
			else if ((_tokenSet_32.member(LA(1))) && (_tokenSet_72.member(LA(2)))) {
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					match(K_POSTPONED);
					break;
				}
				case BASIC_IDENTIFIER:
				case EXTENDED_IDENTIFIER:
				case STRING_LITERAL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				procedure_call();
				match(SEMI);
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void procedure_call() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			name();
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				actual_parameter_part();
				match(RPAREN);
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void concurrent_signal_assignment_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched123 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON))) {
				int _m123 = mark();
				synPredMatched123 = true;
				inputState.guessing++;
				try {
					{
					label_colon();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched123 = false;
				}
				rewind(_m123);
inputState.guessing--;
			}
			if ( synPredMatched123 ) {
				label_colon();
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					match(K_POSTPONED);
					break;
				}
				case LPAREN:
				case BASIC_IDENTIFIER:
				case EXTENDED_IDENTIFIER:
				case K_WITH:
				case STRING_LITERAL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				concurrent_signal_assignment_statement_2();
			}
			else if ((_tokenSet_36.member(LA(1))) && (_tokenSet_73.member(LA(2)))) {
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					match(K_POSTPONED);
					break;
				}
				case LPAREN:
				case BASIC_IDENTIFIER:
				case EXTENDED_IDENTIFIER:
				case K_WITH:
				case STRING_LITERAL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				concurrent_signal_assignment_statement_2();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void concurrent_signal_assignment_statement_2() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				conditional_signal_assignment();
				break;
			}
			case K_WITH:
			{
				selected_signal_assignment();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void conditional_signal_assignment() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			target();
			match(LSTEQ);
			voptions();
			conditional_waveforms();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void selected_signal_assignment() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_WITH);
			expression();
			match(K_SELECT);
			target();
			match(LSTEQ);
			voptions();
			selected_waveforms();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void process_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_POSTPONED:
			case K_PROCESS:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_POSTPONED:
			{
				match(K_POSTPONED);
				break;
			}
			case K_PROCESS:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_PROCESS);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				sensitivity_list();
				match(RPAREN);
				break;
			}
			case K_ALIAS:
			case K_IS:
			case K_BEGIN:
			case K_ATTRIBUTE:
			case K_USE:
			case K_GROUP:
			case K_CONSTANT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_IS:
			{
				match(K_IS);
				break;
			}
			case K_ALIAS:
			case K_BEGIN:
			case K_ATTRIBUTE:
			case K_USE:
			case K_GROUP:
			case K_CONSTANT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			process_declarative_part();
			match(K_BEGIN);
			process_statement_part();
			match(K_END);
			{
			switch ( LA(1)) {
			case K_POSTPONED:
			{
				match(K_POSTPONED);
				break;
			}
			case K_PROCESS:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_PROCESS);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void generate_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			label();
			match(COLON);
			generation_scheme();
			match(K_GENERATE);
			{
			switch ( LA(1)) {
			case K_ALIAS:
			case K_BEGIN:
			case K_ATTRIBUTE:
			case K_USE:
			case K_FOR:
			case K_GROUP:
			case K_COMPONENT:
			case K_CONSTANT:
			case K_DISCONNECT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_SIGNAL:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				{
				_loop265:
				do {
					if ((_tokenSet_22.member(LA(1)))) {
						block_declarative_item();
					}
					else {
						break _loop265;
					}
					
				} while (true);
				}
				match(K_BEGIN);
				break;
			}
			case LPAREN:
			case K_END:
			case K_ASSERT:
			case K_POSTPONED:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_PROCESS:
			case K_WITH:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			_loop267:
			do {
				if ((_tokenSet_24.member(LA(1)))) {
					concurrent_statement();
				}
				else {
					break _loop267;
				}
				
			} while (true);
			}
			match(K_END);
			match(K_GENERATE);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void condition_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_UNTIL);
			condition();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_74);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void target() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				break;
			}
			case LPAREN:
			{
				aggregate();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_75);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void voptions() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_GUARDED:
			{
				match(K_GUARDED);
				break;
			}
			case LPAREN:
			case PLUS:
			case MINUS:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case K_TRANSPORT:
			case K_REJECT:
			case K_INERTIAL:
			case K_ABS:
			case K_NOT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			case K_UNAFFECTED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_TRANSPORT:
			case K_REJECT:
			case K_INERTIAL:
			{
				delay_mechanism();
				break;
			}
			case LPAREN:
			case PLUS:
			case MINUS:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case K_ABS:
			case K_NOT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			case K_UNAFFECTED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_76);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void conditional_waveforms() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			waveform();
			{
			boolean synPredMatched146 = false;
			if (((LA(1)==K_WHEN) && (_tokenSet_10.member(LA(2))))) {
				int _m146 = mark();
				synPredMatched146 = true;
				inputState.guessing++;
				try {
					{
					match(K_WHEN);
					condition();
					match(K_ELSE);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched146 = false;
				}
				rewind(_m146);
inputState.guessing--;
			}
			if ( synPredMatched146 ) {
				conditional_waveforms_2();
			}
			else if ((LA(1)==SEMI||LA(1)==K_WHEN) && (_tokenSet_77.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			{
			switch ( LA(1)) {
			case K_WHEN:
			{
				match(K_WHEN);
				condition();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void waveform() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			case PLUS:
			case MINUS:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case K_ABS:
			case K_NOT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			{
				waveform_element();
				{
				_loop610:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						waveform_element();
					}
					else {
						break _loop610;
					}
					
				} while (true);
				}
				break;
			}
			case K_UNAFFECTED:
			{
				match(K_UNAFFECTED);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_78);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void conditional_waveforms_2() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_WHEN);
			condition();
			match(K_ELSE);
			waveform();
			{
			boolean synPredMatched151 = false;
			if (((LA(1)==K_WHEN) && (_tokenSet_10.member(LA(2))))) {
				int _m151 = mark();
				synPredMatched151 = true;
				inputState.guessing++;
				try {
					{
					match(K_WHEN);
					condition();
					match(K_ELSE);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched151 = false;
				}
				rewind(_m151);
inputState.guessing--;
			}
			if ( synPredMatched151 ) {
				conditional_waveforms_2();
			}
			else if ((LA(1)==SEMI||LA(1)==K_WHEN) && (_tokenSet_77.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_78);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void configuration_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_CONFIGURATION);
			identifier();
			match(K_OF);
			name();
			match(K_IS);
			configuration_declarative_part();
			block_configuration();
			match(K_END);
			{
			switch ( LA(1)) {
			case K_CONFIGURATION:
			{
				match(K_CONFIGURATION);
				break;
			}
			case SEMI:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void configuration_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop158:
			do {
				if ((LA(1)==K_ATTRIBUTE||LA(1)==K_USE||LA(1)==K_GROUP)) {
					configuration_declarative_item();
				}
				else {
					break _loop158;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_79);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void configuration_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_USE:
			{
				use_clause();
				break;
			}
			case K_ATTRIBUTE:
			{
				attribute_specification();
				break;
			}
			case K_GROUP:
			{
				group_declaration();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_80);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void identifier_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			identifier();
			{
			_loop283:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					identifier();
				}
				else {
					break _loop283;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_71);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void index_constraint() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(LPAREN);
			discrete_range();
			{
			_loop293:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					discrete_range();
				}
				else {
					break _loop293;
				}
				
			} while (true);
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_81);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void constraint() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_RANGE:
			{
				range_constraint();
				break;
			}
			case LPAREN:
			{
				index_constraint();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void range_constraint() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_RANGE);
			range();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void context_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop169:
			do {
				if ((LA(1)==K_USE||LA(1)==K_LIBRARY)) {
					context_item();
				}
				else {
					break _loop169;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_82);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void context_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_LIBRARY:
			{
				library_clause();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_83);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void library_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_LIBRARY);
			logical_name_list();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_83);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_ATTRIBUTE:
			{
				attribute_declaration();
				break;
			}
			case K_COMPONENT:
			{
				component_declaration();
				break;
			}
			case K_ENTITY:
			{
				entity_declaration();
				break;
			}
			case K_CONFIGURATION:
			{
				configuration_declaration();
				break;
			}
			case K_PROCEDURE:
			case K_FUNCTION:
			case K_PURE:
			case K_IMPURE:
			{
				subprogram_declaration();
				break;
			}
			case K_PACKAGE:
			{
				package_declaration();
				break;
			}
			default:
				boolean synPredMatched174 = false;
				if (((_tokenSet_84.member(LA(1))) && (LA(2)==K_VARIABLE||LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
					int _m174 = mark();
					synPredMatched174 = true;
					inputState.guessing++;
					try {
						{
						object_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched174 = false;
					}
					rewind(_m174);
inputState.guessing--;
				}
				if ( synPredMatched174 ) {
					object_declaration();
				}
				else if ((_tokenSet_85.member(LA(1))) && (_tokenSet_86.member(LA(2)))) {
					interface_declaration();
				}
				else {
					boolean synPredMatched176 = false;
					if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m176 = mark();
						synPredMatched176 = true;
						inputState.guessing++;
						try {
							{
							match(K_GROUP);
							identifier();
							match(COLON);
							}
						}
						catch (RecognitionException pe) {
							synPredMatched176 = false;
						}
						rewind(_m176);
inputState.guessing--;
					}
					if ( synPredMatched176 ) {
						group_declaration();
					}
					else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						group_template_declaration();
					}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_87);
				} else {
				  throw ex;
				}
			}
		}
		
	public final void object_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_87);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void interface_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched310 = false;
			if (((LA(1)==K_CONSTANT||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_86.member(LA(2))))) {
				int _m310 = mark();
				synPredMatched310 = true;
				inputState.guessing++;
				try {
					{
					interface_constant_declaration();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched310 = false;
				}
				rewind(_m310);
inputState.guessing--;
			}
			if ( synPredMatched310 ) {
				interface_constant_declaration();
			}
			else {
				boolean synPredMatched312 = false;
				if (((LA(1)==K_SIGNAL||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_86.member(LA(2))))) {
					int _m312 = mark();
					synPredMatched312 = true;
					inputState.guessing++;
					try {
						{
						interface_signal_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched312 = false;
					}
					rewind(_m312);
inputState.guessing--;
				}
				if ( synPredMatched312 ) {
					interface_signal_declaration();
				}
				else if ((LA(1)==K_VARIABLE||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_86.member(LA(2)))) {
					interface_variable_declaration();
				}
				else if ((LA(1)==K_FILE)) {
					interface_file_declaration();
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_88);
				} else {
				  throw ex;
				}
			}
		}
		
	public final void entity_declaration() throws RecognitionException, TokenStreamException {
		
		Token id = null;
		
		try {      // for error handling
			match(K_ENTITY);
			id=identifier();
			if ( inputState.guessing==0 ) {
				stTracker.beginEntityDecl(id);
			}
			match(K_IS);
			entity_header();
			entity_declarative_part();
			{
			switch ( LA(1)) {
			case K_BEGIN:
			{
				match(K_BEGIN);
				entity_statement_part();
				break;
			}
			case K_END:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_END);
			{
			switch ( LA(1)) {
			case K_ENTITY:
			{
				match(K_ENTITY);
				break;
			}
			case SEMI:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
			if ( inputState.guessing==0 ) {
				stTracker.endEntityDecl();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void package_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_PACKAGE);
			identifier();
			match(K_IS);
			package_declarative_part();
			match(K_END);
			{
			switch ( LA(1)) {
			case K_PACKAGE:
			{
				match(K_PACKAGE);
				break;
			}
			case SEMI:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void delay_mechanism() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TRANSPORT:
			{
				match(K_TRANSPORT);
				break;
			}
			case K_REJECT:
			case K_INERTIAL:
			{
				{
				switch ( LA(1)) {
				case K_REJECT:
				{
					match(K_REJECT);
					expression();
					break;
				}
				case K_INERTIAL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(K_INERTIAL);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_76);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void design_file() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			int _cnt181=0;
			_loop181:
			do {
				if ((_tokenSet_83.member(LA(1)))) {
					design_unit();
				}
				else {
					if ( _cnt181>=1 ) { break _loop181; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt181++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_87);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void design_unit() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			context_clause();
			library_unit();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void library_unit() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched333 = false;
			if (((LA(1)==K_ARCHITECTURE||LA(1)==K_PACKAGE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER||LA(2)==K_BODY))) {
				int _m333 = mark();
				synPredMatched333 = true;
				inputState.guessing++;
				try {
					{
					switch ( LA(1)) {
					case K_ARCHITECTURE:
					{
						match(K_ARCHITECTURE);
						break;
					}
					case K_PACKAGE:
					{
						match(K_PACKAGE);
						match(K_BODY);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
				}
				catch (RecognitionException pe) {
					synPredMatched333 = false;
				}
				rewind(_m333);
inputState.guessing--;
			}
			if ( synPredMatched333 ) {
				secondary_unit();
			}
			else if ((LA(1)==K_CONFIGURATION||LA(1)==K_ENTITY||LA(1)==K_PACKAGE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
				primary_unit();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void designator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				identifier();
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_89);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void direction() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TO:
			{
				match(K_TO);
				break;
			}
			case K_DOWNTO:
			{
				match(K_DOWNTO);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_10);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void guarded_signal_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			signal_list();
			match(COLON);
			name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_90);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void range() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched466 = false;
			if (((_tokenSet_10.member(LA(1))) && (_tokenSet_91.member(LA(2))))) {
				int _m466 = mark();
				synPredMatched466 = true;
				inputState.guessing++;
				try {
					{
					simple_expression();
					direction();
					simple_expression();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched466 = false;
				}
				rewind(_m466);
inputState.guessing--;
			}
			if ( synPredMatched466 ) {
				simple_expression();
				direction();
				simple_expression();
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_92.member(LA(2)))) {
				name();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void element_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			identifier_list();
			match(COLON);
			element_subtype_definition();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_47);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void element_subtype_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			subtype_indication();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_class() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ENTITY:
			{
				match(K_ENTITY);
				break;
			}
			case K_PROCEDURE:
			{
				match(K_PROCEDURE);
				break;
			}
			case K_TYPE:
			{
				match(K_TYPE);
				break;
			}
			case K_SIGNAL:
			{
				match(K_SIGNAL);
				break;
			}
			case K_LABEL:
			{
				match(K_LABEL);
				break;
			}
			case K_ARCHITECTURE:
			{
				match(K_ARCHITECTURE);
				break;
			}
			case K_FUNCTION:
			{
				match(K_FUNCTION);
				break;
			}
			case K_SUBTYPE:
			{
				match(K_SUBTYPE);
				break;
			}
			case K_VARIABLE:
			{
				match(K_VARIABLE);
				break;
			}
			case K_LITERAL:
			{
				match(K_LITERAL);
				break;
			}
			case K_CONFIGURATION:
			{
				match(K_CONFIGURATION);
				break;
			}
			case K_PACKAGE:
			{
				match(K_PACKAGE);
				break;
			}
			case K_CONSTANT:
			{
				match(K_CONSTANT);
				break;
			}
			case K_COMPONENT:
			{
				match(K_COMPONENT);
				break;
			}
			case K_UNITS:
			{
				match(K_UNITS);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_93);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_class_entry() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			entity_class();
			{
			switch ( LA(1)) {
			case LSTGRT:
			{
				match(LSTGRT);
				break;
			}
			case RPAREN:
			case COMMA:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_class_entry_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			entity_class_entry();
			{
			_loop202:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					entity_class_entry();
				}
				else {
					break _loop202;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_header() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_clause();
				break;
			}
			case K_ALIAS:
			case K_BEGIN:
			case K_END:
			case K_ATTRIBUTE:
			case K_USE:
			case K_GROUP:
			case K_CONSTANT:
			case K_DISCONNECT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_SIGNAL:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_PORT:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_PORT:
			{
				port_clause();
				break;
			}
			case K_ALIAS:
			case K_BEGIN:
			case K_END:
			case K_ATTRIBUTE:
			case K_USE:
			case K_GROUP:
			case K_CONSTANT:
			case K_DISCONNECT:
			case K_PROCEDURE:
			case K_TYPE:
			case K_SIGNAL:
			case K_FUNCTION:
			case K_SUBTYPE:
			case K_VARIABLE:
			case K_FILE:
			case K_PURE:
			case K_IMPURE:
			case K_SHARED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_94);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop216:
			do {
				if ((_tokenSet_95.member(LA(1)))) {
					entity_declarative_item();
				}
				else {
					break _loop216;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_96);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_statement_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop233:
			do {
				if ((_tokenSet_97.member(LA(1)))) {
					entity_statement();
				}
				else {
					break _loop233;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_DISCONNECT:
			{
				disconnection_specification();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
				boolean synPredMatched209 = false;
				if (((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2))))) {
					int _m209 = mark();
					synPredMatched209 = true;
					inputState.guessing++;
					try {
						{
						subprogram_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched209 = false;
					}
					rewind(_m209);
inputState.guessing--;
				}
				if ( synPredMatched209 ) {
					subprogram_declaration();
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
				}
				else {
					boolean synPredMatched211 = false;
					if (((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m211 = mark();
						synPredMatched211 = true;
						inputState.guessing++;
						try {
							{
							attribute_specification();
							}
						}
						catch (RecognitionException pe) {
							synPredMatched211 = false;
						}
						rewind(_m211);
inputState.guessing--;
					}
					if ( synPredMatched211 ) {
						attribute_specification();
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
					}
					else {
						boolean synPredMatched213 = false;
						if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
							int _m213 = mark();
							synPredMatched213 = true;
							inputState.guessing++;
							try {
								{
								match(K_GROUP);
								identifier();
								match(COLON);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched213 = false;
							}
							rewind(_m213);
inputState.guessing--;
						}
						if ( synPredMatched213 ) {
							group_declaration();
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
						}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					}}}
				}
				catch (RecognitionException ex) {
					if (inputState.guessing==0) {
						reportError(ex);
						recover(ex,_tokenSet_94);
					} else {
					  throw ex;
					}
				}
			}
			
	public final void entity_designator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			entity_tag();
			{
			switch ( LA(1)) {
			case LBRACK:
			{
				signature();
				break;
			}
			case COMMA:
			case COLON:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_98);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_tag() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_99);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_name_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case CHARACTER_LITERAL:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				entity_designator();
				{
				_loop224:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						entity_designator();
					}
					else {
						break _loop224;
					}
					
				} while (true);
				}
				break;
			}
			case K_OTHERS:
			{
				match(K_OTHERS);
				break;
			}
			case K_ALL:
			{
				match(K_ALL);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_71);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void entity_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched228 = false;
			if (((_tokenSet_34.member(LA(1))) && (_tokenSet_35.member(LA(2))))) {
				int _m228 = mark();
				synPredMatched228 = true;
				inputState.guessing++;
				try {
					{
					concurrent_assertion_statement();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched228 = false;
				}
				rewind(_m228);
inputState.guessing--;
			}
			if ( synPredMatched228 ) {
				concurrent_assertion_statement();
			}
			else {
				boolean synPredMatched230 = false;
				if (((_tokenSet_32.member(LA(1))) && (_tokenSet_33.member(LA(2))))) {
					int _m230 = mark();
					synPredMatched230 = true;
					inputState.guessing++;
					try {
						{
						concurrent_procedure_call_statement();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched230 = false;
					}
					rewind(_m230);
inputState.guessing--;
				}
				if ( synPredMatched230 ) {
					concurrent_procedure_call_statement();
				}
				else if ((_tokenSet_30.member(LA(1))) && (_tokenSet_31.member(LA(2)))) {
					process_statement();
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_100);
				} else {
				  throw ex;
				}
			}
		}
		
	public final void enumeration_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				identifier();
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void enumeration_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(LPAREN);
			enumeration_literal();
			{
			_loop238:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					enumeration_literal();
				}
				else {
					break _loop238;
				}
				
			} while (true);
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void exit_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_EXIT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_EXIT);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			case K_WHEN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_WHEN:
			{
				match(K_WHEN);
				condition();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void relation() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			shift_expression();
			{
			switch ( LA(1)) {
			case LSTEQ:
			case EQ:
			case SLASHEQ:
			case LST:
			case GRT:
			case GRTEQ:
			{
				relational_operator();
				shift_expression();
				break;
			}
			case EOF:
			case RPAREN:
			case COMMA:
			case K_IS:
			case SEMI:
			case K_REPORT:
			case K_SEVERITY:
			case K_FOR:
			case K_WHEN:
			case K_ELSE:
			case K_INERTIAL:
			case K_AFTER:
			case K_AND:
			case K_OR:
			case K_XOR:
			case K_NAND:
			case K_NOR:
			case K_XNOR:
			case K_GENERATE:
			case K_THEN:
			case K_LOOP:
			case K_SELECT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_101);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void logical_op() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_AND:
			{
				match(K_AND);
				break;
			}
			case K_OR:
			{
				match(K_OR);
				break;
			}
			case K_XOR:
			{
				match(K_XOR);
				break;
			}
			case K_NAND:
			{
				match(K_NAND);
				break;
			}
			case K_NOR:
			{
				match(K_NOR);
				break;
			}
			case K_XNOR:
			{
				match(K_XNOR);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_10);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void factor() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			{
				primary();
				{
				if ((LA(1)==STAR2) && (_tokenSet_102.member(LA(2)))) {
					match(STAR2);
					primary();
				}
				else if ((_tokenSet_2.member(LA(1))) && (_tokenSet_103.member(LA(2)))) {
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
				break;
			}
			case K_ABS:
			{
				match(K_ABS);
				primary();
				break;
			}
			case K_NOT:
			{
				match(K_NOT);
				primary();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void primary() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched407 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_92.member(LA(2))))) {
				int _m407 = mark();
				synPredMatched407 = true;
				inputState.guessing++;
				try {
					{
					function_call();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched407 = false;
				}
				rewind(_m407);
inputState.guessing--;
			}
			if ( synPredMatched407 ) {
				function_call();
			}
			else {
				boolean synPredMatched410 = false;
				if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_6.member(LA(2))))) {
					int _m410 = mark();
					synPredMatched410 = true;
					inputState.guessing++;
					try {
						{
						name();
						{
						switch ( LA(1)) {
						case LBRACK:
						{
							signature();
							break;
						}
						case TIC_SIMPLE_NAME:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						tic_attribute_designator();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched410 = false;
					}
					rewind(_m410);
inputState.guessing--;
				}
				if ( synPredMatched410 ) {
					name();
					{
					switch ( LA(1)) {
					case LBRACK:
					{
						signature();
						break;
					}
					case TIC_SIMPLE_NAME:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					tic_attribute_designator();
				}
				else {
					boolean synPredMatched413 = false;
					if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_6.member(LA(2))))) {
						int _m413 = mark();
						synPredMatched413 = true;
						inputState.guessing++;
						try {
							{
							name();
							match(TIC);
							}
						}
						catch (RecognitionException pe) {
							synPredMatched413 = false;
						}
						rewind(_m413);
inputState.guessing--;
					}
					if ( synPredMatched413 ) {
						qualified_expression();
					}
					else {
						boolean synPredMatched415 = false;
						if (((LA(1)==LPAREN) && (_tokenSet_10.member(LA(2))))) {
							int _m415 = mark();
							synPredMatched415 = true;
							inputState.guessing++;
							try {
								{
								match(LPAREN);
								expression();
								match(RPAREN);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched415 = false;
							}
							rewind(_m415);
inputState.guessing--;
						}
						if ( synPredMatched415 ) {
							match(LPAREN);
							expression();
							match(RPAREN);
						}
						else if ((_tokenSet_104.member(LA(1))) && (_tokenSet_105.member(LA(2)))) {
							literal();
						}
						else if ((LA(1)==K_NEW)) {
							allocator();
						}
						else if ((LA(1)==LPAREN) && (_tokenSet_14.member(LA(2)))) {
							aggregate();
						}
						else {
							throw new NoViableAltException(LT(1), getFilename());
						}
						}}}
					}
					catch (RecognitionException ex) {
						if (inputState.guessing==0) {
							reportError(ex);
							recover(ex,_tokenSet_2);
						} else {
						  throw ex;
						}
					}
				}
				
	public final void file_open_information() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_OPEN:
			{
				match(K_OPEN);
				expression();
				break;
			}
			case K_IS:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_IS);
			file_logical_name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void file_logical_name() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			expression();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void file_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_FILE);
			match(K_OF);
			name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void floating_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			range_constraint();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_87);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void formal_parameter_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			interface_list();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void interface_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			interface_element();
			{
			_loop317:
			do {
				if ((LA(1)==SEMI)) {
					match(SEMI);
					interface_element();
				}
				else {
					break _loop317;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void full_type_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_TYPE);
			identifier();
			match(K_IS);
			type_definition();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			case K_RANGE:
			{
				scalar_type_definition();
				break;
			}
			case K_ARRAY:
			case K_RECORD:
			{
				composite_type_definition();
				break;
			}
			case K_ACCESS:
			{
				access_type_definition();
				break;
			}
			case K_FILE:
			{
				file_type_definition();
				break;
			}
			case K_PROTECTED:
			{
				protected_type_definition();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void function_call() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			name();
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				actual_parameter_part();
				match(RPAREN);
				break;
			}
			case EOF:
			case K_OPEN:
			case RPAREN:
			case PLUS:
			case MINUS:
			case AND:
			case COMMA:
			case K_IS:
			case SEMI:
			case K_REPORT:
			case K_SEVERITY:
			case EQGRT:
			case K_FOR:
			case K_WHEN:
			case BAR:
			case LSTEQ:
			case K_ELSE:
			case COLONEQ:
			case K_INERTIAL:
			case K_TO:
			case K_DOWNTO:
			case K_AFTER:
			case K_UNITS:
			case K_AND:
			case K_OR:
			case K_XOR:
			case K_NAND:
			case K_NOR:
			case K_XNOR:
			case STAR2:
			case K_GENERATE:
			case K_THEN:
			case K_BUS:
			case K_LOOP:
			case STAR:
			case SLASH:
			case K_MOD:
			case K_REM:
			case EQ:
			case SLASHEQ:
			case LST:
			case GRT:
			case GRTEQ:
			case K_SELECT:
			case K_SLL:
			case K_SRL:
			case K_SLA:
			case K_SRA:
			case K_ROL:
			case K_ROR:
			case K_REGISTER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void generation_scheme() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_FOR:
			{
				match(K_FOR);
				parameter_specification();
				break;
			}
			case K_IF:
			{
				match(K_IF);
				condition();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_106);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void parameter_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			identifier();
			match(K_IN);
			discrete_range();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_107);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void generic_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			interface_list();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void group_constituent() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void group_constituent_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			group_constituent();
			{
			_loop276:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					group_constituent();
				}
				else {
					break _loop276;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void signal_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				{
				_loop544:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						name();
					}
					else {
						break _loop544;
					}
					
				} while (true);
				}
				break;
			}
			case K_OTHERS:
			{
				match(K_OTHERS);
				break;
			}
			case K_ALL:
			{
				match(K_ALL);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_71);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void if_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_IF:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_IF);
			condition();
			match(K_THEN);
			sequence_of_statements();
			{
			_loop287:
			do {
				if ((LA(1)==K_ELSIF)) {
					match(K_ELSIF);
					condition();
					match(K_THEN);
					sequence_of_statements();
				}
				else {
					break _loop287;
				}
				
			} while (true);
			}
			{
			switch ( LA(1)) {
			case K_ELSE:
			{
				match(K_ELSE);
				sequence_of_statements();
				break;
			}
			case K_END:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_END);
			match(K_IF);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void incomplete_type_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_TYPE);
			identifier();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void index_subtype_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			name();
			match(K_RANGE);
			match(LSTGRT);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void interface_constant_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_CONSTANT:
			{
				match(K_CONSTANT);
				break;
			}
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			identifier_list();
			match(COLON);
			{
			switch ( LA(1)) {
			case K_IN:
			{
				match(K_IN);
				break;
			}
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			subtype_indication();
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				match(COLONEQ);
				expression();
				break;
			}
			case EOF:
			case RPAREN:
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void interface_signal_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_SIGNAL:
			{
				match(K_SIGNAL);
				break;
			}
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			identifier_list();
			match(COLON);
			{
			switch ( LA(1)) {
			case K_IN:
			case K_OUT:
			case K_INOUT:
			case K_BUFFER:
			case K_LINKAGE:
			{
				mode();
				break;
			}
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			subtype_indication();
			{
			switch ( LA(1)) {
			case K_BUS:
			{
				match(K_BUS);
				break;
			}
			case EOF:
			case RPAREN:
			case SEMI:
			case COLONEQ:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				match(COLONEQ);
				expression();
				break;
			}
			case EOF:
			case RPAREN:
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void interface_variable_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_VARIABLE:
			{
				match(K_VARIABLE);
				break;
			}
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			identifier_list();
			match(COLON);
			{
			switch ( LA(1)) {
			case K_IN:
			case K_OUT:
			case K_INOUT:
			case K_BUFFER:
			case K_LINKAGE:
			{
				mode();
				break;
			}
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			subtype_indication();
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				match(COLONEQ);
				expression();
				break;
			}
			case EOF:
			case RPAREN:
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void interface_file_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_FILE);
			identifier_list();
			match(COLON);
			subtype_indication();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void interface_element() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			interface_declaration();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_108);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void mode() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_IN:
			{
				match(K_IN);
				break;
			}
			case K_OUT:
			{
				match(K_OUT);
				break;
			}
			case K_INOUT:
			{
				match(K_INOUT);
				break;
			}
			case K_BUFFER:
			{
				match(K_BUFFER);
				break;
			}
			case K_LINKAGE:
			{
				match(K_LINKAGE);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_109);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void iteration_scheme() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_WHILE:
			{
				match(K_WHILE);
				condition();
				break;
			}
			case K_FOR:
			{
				match(K_FOR);
				parameter_specification();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_110);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void logical_name_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			logical_name();
			{
			_loop340:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					logical_name();
				}
				else {
					break _loop340;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void secondary_unit() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ARCHITECTURE:
			{
				architecture_body();
				break;
			}
			case K_PACKAGE:
			{
				package_body();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void primary_unit() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ENTITY:
			{
				entity_declaration();
				break;
			}
			case K_CONFIGURATION:
			{
				configuration_declaration();
				break;
			}
			case K_PACKAGE:
			{
				package_declaration();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case BIT_STRING_LITERAL:
			{
				bit_string_literal();
				break;
			}
			case K_NULL:
			{
				match(K_NULL);
				break;
			}
			default:
				boolean synPredMatched336 = false;
				if (((_tokenSet_111.member(LA(1))) && (_tokenSet_105.member(LA(2))))) {
					int _m336 = mark();
					synPredMatched336 = true;
					inputState.guessing++;
					try {
						{
						numeric_literal();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched336 = false;
					}
					rewind(_m336);
inputState.guessing--;
				}
				if ( synPredMatched336 ) {
					numeric_literal();
				}
				else if ((LA(1)==CHARACTER_LITERAL||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_2.member(LA(2)))) {
					enumeration_literal();
				}
				else if ((LA(1)==STRING_LITERAL) && (_tokenSet_2.member(LA(2)))) {
					string_literal();
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void numeric_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched371 = false;
			if (((LA(1)==BASED_LITERAL||LA(1)==DECIMAL_LITERAL) && (_tokenSet_2.member(LA(2))))) {
				int _m371 = mark();
				synPredMatched371 = true;
				inputState.guessing++;
				try {
					{
					abstract_literal();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched371 = false;
				}
				rewind(_m371);
inputState.guessing--;
			}
			if ( synPredMatched371 ) {
				abstract_literal();
			}
			else if ((_tokenSet_111.member(LA(1))) && (_tokenSet_105.member(LA(2)))) {
				physical_literal();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void string_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(STRING_LITERAL);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void logical_name() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			identifier();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_112);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void logical_operator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_AND:
			{
				match(K_AND);
				break;
			}
			case K_OR:
			{
				match(K_OR);
				break;
			}
			case K_NAND:
			{
				match(K_NAND);
				break;
			}
			case K_NOR:
			{
				match(K_NOR);
				break;
			}
			case K_XOR:
			{
				match(K_XOR);
				break;
			}
			case K_XNOR:
			{
				match(K_XNOR);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_87);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void loop_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_FOR:
			case K_WHILE:
			case K_LOOP:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_FOR:
			case K_WHILE:
			{
				iteration_scheme();
				break;
			}
			case K_LOOP:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_LOOP);
			sequence_of_statements();
			match(K_END);
			match(K_LOOP);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void miscellaneous_operator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case STAR2:
			{
				match(STAR2);
				break;
			}
			case K_ABS:
			{
				match(K_ABS);
				break;
			}
			case K_NOT:
			{
				match(K_NOT);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_87);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void multiplying_operator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case STAR:
			{
				match(STAR);
				break;
			}
			case SLASH:
			{
				match(SLASH);
				break;
			}
			case K_MOD:
			{
				match(K_MOD);
				break;
			}
			case K_REM:
			{
				match(K_REM);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_12);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Token  suffix() throws RecognitionException, TokenStreamException {
		Token tok;
		
		tok=null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				tok=simple_name();
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				break;
			}
			case K_ALL:
			{
				match(K_ALL);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		return tok;
	}
	
	public final void next_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_NEXT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_NEXT);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				break;
			}
			case SEMI:
			case K_WHEN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_WHEN:
			{
				match(K_WHEN);
				condition();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void null_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_NULL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_NULL);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void physical_literal() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASED_LITERAL:
			case DECIMAL_LITERAL:
			{
				abstract_literal();
				break;
			}
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			name();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void package_body() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_PACKAGE);
			match(K_BODY);
			simple_name();
			match(K_IS);
			package_body_declarative_part();
			match(K_END);
			{
			switch ( LA(1)) {
			case K_PACKAGE:
			{
				match(K_PACKAGE);
				match(K_BODY);
				break;
			}
			case SEMI:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void package_body_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop384:
			do {
				if ((_tokenSet_113.member(LA(1)))) {
					package_body_declarative_item();
				}
				else {
					break _loop384;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void package_body_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
				boolean synPredMatched379 = false;
				if (((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2))))) {
					int _m379 = mark();
					synPredMatched379 = true;
					inputState.guessing++;
					try {
						{
						subprogram_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched379 = false;
					}
					rewind(_m379);
inputState.guessing--;
				}
				if ( synPredMatched379 ) {
					subprogram_declaration();
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
				}
				else {
					boolean synPredMatched381 = false;
					if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m381 = mark();
						synPredMatched381 = true;
						inputState.guessing++;
						try {
							{
							match(K_GROUP);
							identifier();
							match(COLON);
							}
						}
						catch (RecognitionException pe) {
							synPredMatched381 = false;
						}
						rewind(_m381);
inputState.guessing--;
					}
					if ( synPredMatched381 ) {
						group_declaration();
					}
					else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						group_template_declaration();
					}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_114);
				} else {
				  throw ex;
				}
			}
		}
		
	public final void package_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop395:
			do {
				if ((_tokenSet_115.member(LA(1)))) {
					package_declarative_item();
				}
				else {
					break _loop395;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void package_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			case K_FUNCTION:
			case K_PURE:
			case K_IMPURE:
			{
				subprogram_declaration();
				break;
			}
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_COMPONENT:
			{
				component_declaration();
				break;
			}
			case K_DISCONNECT:
			{
				disconnection_specification();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
				boolean synPredMatched390 = false;
				if (((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
					int _m390 = mark();
					synPredMatched390 = true;
					inputState.guessing++;
					try {
						{
						attribute_specification();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched390 = false;
					}
					rewind(_m390);
inputState.guessing--;
				}
				if ( synPredMatched390 ) {
					attribute_specification();
				}
				else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
					attribute_declaration();
				}
				else {
					boolean synPredMatched392 = false;
					if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m392 = mark();
						synPredMatched392 = true;
						inputState.guessing++;
						try {
							{
							match(K_GROUP);
							identifier();
							match(COLON);
							}
						}
						catch (RecognitionException pe) {
							synPredMatched392 = false;
						}
						rewind(_m392);
inputState.guessing--;
					}
					if ( synPredMatched392 ) {
						group_declaration();
					}
					else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						group_template_declaration();
					}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_116);
				} else {
				  throw ex;
				}
			}
		}
		
	public final void physical_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			range_constraint();
			match(K_UNITS);
			base_unit_declaration();
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				secondary_unit_declaration();
				break;
			}
			case K_END:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_END);
			match(K_UNITS);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void secondary_unit_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			identifier();
			match(EQ);
			physical_literal();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void port_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			interface_list();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void procedure_call_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
				label_colon();
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_117.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			procedure_call();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void process_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
				boolean synPredMatched423 = false;
				if (((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2))))) {
					int _m423 = mark();
					synPredMatched423 = true;
					inputState.guessing++;
					try {
						{
						subprogram_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched423 = false;
					}
					rewind(_m423);
inputState.guessing--;
				}
				if ( synPredMatched423 ) {
					subprogram_declaration();
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
				}
				else {
					boolean synPredMatched425 = false;
					if (((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m425 = mark();
						synPredMatched425 = true;
						inputState.guessing++;
						try {
							{
							attribute_specification();
							}
						}
						catch (RecognitionException pe) {
							synPredMatched425 = false;
						}
						rewind(_m425);
inputState.guessing--;
					}
					if ( synPredMatched425 ) {
						attribute_specification();
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
					}
					else {
						boolean synPredMatched427 = false;
						if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
							int _m427 = mark();
							synPredMatched427 = true;
							inputState.guessing++;
							try {
								{
								match(K_GROUP);
								identifier();
								match(COLON);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched427 = false;
							}
							rewind(_m427);
inputState.guessing--;
						}
						if ( synPredMatched427 ) {
							group_declaration();
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
						}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					}}}
				}
				catch (RecognitionException ex) {
					if (inputState.guessing==0) {
						reportError(ex);
						recover(ex,_tokenSet_118);
					} else {
					  throw ex;
					}
				}
			}
			
	public final void process_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop430:
			do {
				if ((_tokenSet_119.member(LA(1)))) {
					process_declarative_item();
				}
				else {
					break _loop430;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void sensitivity_list() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			name();
			{
			_loop493:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					name();
				}
				else {
					break _loop493;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_120);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void process_statement_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop440:
			do {
				if ((_tokenSet_62.member(LA(1)))) {
					sequential_statement();
				}
				else {
					break _loop440;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void sequential_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			boolean synPredMatched500 = false;
			if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==K_WAIT) && (_tokenSet_121.member(LA(2))))) {
				int _m500 = mark();
				synPredMatched500 = true;
				inputState.guessing++;
				try {
					{
					{
					switch ( LA(1)) {
					case BASIC_IDENTIFIER:
					case EXTENDED_IDENTIFIER:
					{
						label_colon();
						break;
					}
					case K_WAIT:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					match(K_WAIT);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched500 = false;
				}
				rewind(_m500);
inputState.guessing--;
			}
			if ( synPredMatched500 ) {
				wait_statement();
			}
			else {
				boolean synPredMatched503 = false;
				if (((LA(1)==K_ASSERT||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_122.member(LA(2))))) {
					int _m503 = mark();
					synPredMatched503 = true;
					inputState.guessing++;
					try {
						{
						{
						switch ( LA(1)) {
						case BASIC_IDENTIFIER:
						case EXTENDED_IDENTIFIER:
						{
							label_colon();
							break;
						}
						case K_ASSERT:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(LT(1), getFilename());
						}
						}
						}
						match(K_ASSERT);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched503 = false;
					}
					rewind(_m503);
inputState.guessing--;
				}
				if ( synPredMatched503 ) {
					assertion_statement();
				}
				else {
					boolean synPredMatched506 = false;
					if (((LA(1)==K_REPORT||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_122.member(LA(2))))) {
						int _m506 = mark();
						synPredMatched506 = true;
						inputState.guessing++;
						try {
							{
							{
							switch ( LA(1)) {
							case BASIC_IDENTIFIER:
							case EXTENDED_IDENTIFIER:
							{
								label_colon();
								break;
							}
							case K_REPORT:
							{
								break;
							}
							default:
							{
								throw new NoViableAltException(LT(1), getFilename());
							}
							}
							}
							match(K_REPORT);
							}
						}
						catch (RecognitionException pe) {
							synPredMatched506 = false;
						}
						rewind(_m506);
inputState.guessing--;
					}
					if ( synPredMatched506 ) {
						report_statement();
					}
					else {
						boolean synPredMatched509 = false;
						if (((LA(1)==K_IF||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_122.member(LA(2))))) {
							int _m509 = mark();
							synPredMatched509 = true;
							inputState.guessing++;
							try {
								{
								{
								switch ( LA(1)) {
								case BASIC_IDENTIFIER:
								case EXTENDED_IDENTIFIER:
								{
									label_colon();
									break;
								}
								case K_IF:
								{
									break;
								}
								default:
								{
									throw new NoViableAltException(LT(1), getFilename());
								}
								}
								}
								match(K_IF);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched509 = false;
							}
							rewind(_m509);
inputState.guessing--;
						}
						if ( synPredMatched509 ) {
							if_statement();
						}
						else {
							boolean synPredMatched512 = false;
							if (((LA(1)==K_CASE||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_122.member(LA(2))))) {
								int _m512 = mark();
								synPredMatched512 = true;
								inputState.guessing++;
								try {
									{
									{
									switch ( LA(1)) {
									case BASIC_IDENTIFIER:
									case EXTENDED_IDENTIFIER:
									{
										label_colon();
										break;
									}
									case K_CASE:
									{
										break;
									}
									default:
									{
										throw new NoViableAltException(LT(1), getFilename());
									}
									}
									}
									match(K_CASE);
									}
								}
								catch (RecognitionException pe) {
									synPredMatched512 = false;
								}
								rewind(_m512);
inputState.guessing--;
							}
							if ( synPredMatched512 ) {
								case_statement();
							}
							else {
								boolean synPredMatched515 = false;
								if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==K_NEXT) && (_tokenSet_123.member(LA(2))))) {
									int _m515 = mark();
									synPredMatched515 = true;
									inputState.guessing++;
									try {
										{
										{
										switch ( LA(1)) {
										case BASIC_IDENTIFIER:
										case EXTENDED_IDENTIFIER:
										{
											label_colon();
											break;
										}
										case K_NEXT:
										{
											break;
										}
										default:
										{
											throw new NoViableAltException(LT(1), getFilename());
										}
										}
										}
										match(K_NEXT);
										}
									}
									catch (RecognitionException pe) {
										synPredMatched515 = false;
									}
									rewind(_m515);
inputState.guessing--;
								}
								if ( synPredMatched515 ) {
									next_statement();
								}
								else {
									boolean synPredMatched518 = false;
									if (((LA(1)==K_EXIT||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_123.member(LA(2))))) {
										int _m518 = mark();
										synPredMatched518 = true;
										inputState.guessing++;
										try {
											{
											{
											switch ( LA(1)) {
											case BASIC_IDENTIFIER:
											case EXTENDED_IDENTIFIER:
											{
												label_colon();
												break;
											}
											case K_EXIT:
											{
												break;
											}
											default:
											{
												throw new NoViableAltException(LT(1), getFilename());
											}
											}
											}
											match(K_EXIT);
											}
										}
										catch (RecognitionException pe) {
											synPredMatched518 = false;
										}
										rewind(_m518);
inputState.guessing--;
									}
									if ( synPredMatched518 ) {
										exit_statement();
									}
									else {
										boolean synPredMatched521 = false;
										if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==K_RETURN) && (_tokenSet_124.member(LA(2))))) {
											int _m521 = mark();
											synPredMatched521 = true;
											inputState.guessing++;
											try {
												{
												{
												switch ( LA(1)) {
												case BASIC_IDENTIFIER:
												case EXTENDED_IDENTIFIER:
												{
													label_colon();
													break;
												}
												case K_RETURN:
												{
													break;
												}
												default:
												{
													throw new NoViableAltException(LT(1), getFilename());
												}
												}
												}
												match(K_RETURN);
												}
											}
											catch (RecognitionException pe) {
												synPredMatched521 = false;
											}
											rewind(_m521);
inputState.guessing--;
										}
										if ( synPredMatched521 ) {
											return_statement();
										}
										else {
											boolean synPredMatched524 = false;
											if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==K_NULL) && (LA(2)==COLON||LA(2)==SEMI))) {
												int _m524 = mark();
												synPredMatched524 = true;
												inputState.guessing++;
												try {
													{
													{
													switch ( LA(1)) {
													case BASIC_IDENTIFIER:
													case EXTENDED_IDENTIFIER:
													{
														label_colon();
														break;
													}
													case K_NULL:
													{
														break;
													}
													default:
													{
														throw new NoViableAltException(LT(1), getFilename());
													}
													}
													}
													match(K_NULL);
													}
												}
												catch (RecognitionException pe) {
													synPredMatched524 = false;
												}
												rewind(_m524);
inputState.guessing--;
											}
											if ( synPredMatched524 ) {
												null_statement();
											}
											else {
												boolean synPredMatched526 = false;
												if (((_tokenSet_125.member(LA(1))) && (_tokenSet_126.member(LA(2))))) {
													int _m526 = mark();
													synPredMatched526 = true;
													inputState.guessing++;
													try {
														{
														loop_statement();
														}
													}
													catch (RecognitionException pe) {
														synPredMatched526 = false;
													}
													rewind(_m526);
inputState.guessing--;
												}
												if ( synPredMatched526 ) {
													loop_statement();
												}
												else {
													boolean synPredMatched528 = false;
													if (((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_127.member(LA(2))))) {
														int _m528 = mark();
														synPredMatched528 = true;
														inputState.guessing++;
														try {
															{
															procedure_call_statement();
															}
														}
														catch (RecognitionException pe) {
															synPredMatched528 = false;
														}
														rewind(_m528);
inputState.guessing--;
													}
													if ( synPredMatched528 ) {
														procedure_call_statement();
													}
													else {
														boolean synPredMatched530 = false;
														if (((_tokenSet_128.member(LA(1))) && (_tokenSet_129.member(LA(2))))) {
															int _m530 = mark();
															synPredMatched530 = true;
															inputState.guessing++;
															try {
																{
																variable_assignment_statement();
																}
															}
															catch (RecognitionException pe) {
																synPredMatched530 = false;
															}
															rewind(_m530);
inputState.guessing--;
														}
														if ( synPredMatched530 ) {
															variable_assignment_statement();
														}
														else if ((_tokenSet_128.member(LA(1))) && (_tokenSet_130.member(LA(2)))) {
															signal_assignment_statement();
														}
														else {
															throw new NoViableAltException(LT(1), getFilename());
														}
														}}}}}}}}}}}
													}
													catch (RecognitionException ex) {
														if (inputState.guessing==0) {
															reportError(ex);
															recover(ex,_tokenSet_40);
														} else {
														  throw ex;
														}
													}
												}
												
	public final void protected_type_body() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_PROTECTED);
			match(K_BODY);
			protected_type_body_declarative_part();
			match(K_END);
			match(K_PROTECTED);
			match(K_BODY);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void protected_type_body_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop452:
			do {
				if ((_tokenSet_119.member(LA(1)))) {
					protected_type_body_declarative_item();
				}
				else {
					break _loop452;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void protected_type_body_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
				boolean synPredMatched445 = false;
				if (((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2))))) {
					int _m445 = mark();
					synPredMatched445 = true;
					inputState.guessing++;
					try {
						{
						subprogram_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched445 = false;
					}
					rewind(_m445);
inputState.guessing--;
				}
				if ( synPredMatched445 ) {
					subprogram_declaration();
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
				}
				else {
					boolean synPredMatched447 = false;
					if (((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m447 = mark();
						synPredMatched447 = true;
						inputState.guessing++;
						try {
							{
							attribute_specification();
							}
						}
						catch (RecognitionException pe) {
							synPredMatched447 = false;
						}
						rewind(_m447);
inputState.guessing--;
					}
					if ( synPredMatched447 ) {
						attribute_specification();
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
					}
					else {
						boolean synPredMatched449 = false;
						if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
							int _m449 = mark();
							synPredMatched449 = true;
							inputState.guessing++;
							try {
								{
								match(K_GROUP);
								identifier();
								match(COLON);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched449 = false;
							}
							rewind(_m449);
inputState.guessing--;
						}
						if ( synPredMatched449 ) {
							group_declaration();
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
						}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					}}}
				}
				catch (RecognitionException ex) {
					if (inputState.guessing==0) {
						reportError(ex);
						recover(ex,_tokenSet_131);
					} else {
					  throw ex;
					}
				}
			}
			
	public final void protected_type_declaration() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_PROTECTED);
			protected_type_declarative_part();
			match(K_END);
			match(K_PROTECTED);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void protected_type_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop458:
			do {
				if ((_tokenSet_132.member(LA(1)))) {
					protected_type_declarative_item();
				}
				else {
					break _loop458;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void protected_type_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			case K_FUNCTION:
			case K_PURE:
			case K_IMPURE:
			{
				subprogram_specification();
				break;
			}
			case K_ATTRIBUTE:
			{
				attribute_specification();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_133);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subprogram_specification() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			{
				match(K_PROCEDURE);
				designator();
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					match(LPAREN);
					formal_parameter_list();
					match(RPAREN);
					break;
				}
				case K_IS:
				case SEMI:
				case K_END:
				case K_ATTRIBUTE:
				case K_USE:
				case K_PROCEDURE:
				case K_FUNCTION:
				case K_PURE:
				case K_IMPURE:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				break;
			}
			case K_FUNCTION:
			case K_PURE:
			case K_IMPURE:
			{
				{
				switch ( LA(1)) {
				case K_PURE:
				{
					match(K_PURE);
					break;
				}
				case K_IMPURE:
				{
					match(K_IMPURE);
					break;
				}
				case K_FUNCTION:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(K_FUNCTION);
				designator();
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					match(LPAREN);
					formal_parameter_list();
					match(RPAREN);
					break;
				}
				case K_RETURN:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(K_RETURN);
				name();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_134);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void protected_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if ((LA(1)==K_PROTECTED) && (_tokenSet_133.member(LA(2)))) {
				protected_type_declaration();
			}
			else if ((LA(1)==K_PROTECTED) && (LA(2)==K_BODY)) {
				protected_type_body();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void shift_expression() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			simple_expression();
			{
			switch ( LA(1)) {
			case K_SLL:
			case K_SRL:
			case K_SLA:
			case K_SRA:
			case K_ROL:
			case K_ROR:
			{
				shift_operator();
				simple_expression();
				break;
			}
			case EOF:
			case RPAREN:
			case COMMA:
			case K_IS:
			case SEMI:
			case K_REPORT:
			case K_SEVERITY:
			case K_FOR:
			case K_WHEN:
			case LSTEQ:
			case K_ELSE:
			case K_INERTIAL:
			case K_AFTER:
			case K_AND:
			case K_OR:
			case K_XOR:
			case K_NAND:
			case K_NOR:
			case K_XNOR:
			case K_GENERATE:
			case K_THEN:
			case K_LOOP:
			case EQ:
			case SLASHEQ:
			case LST:
			case GRT:
			case GRTEQ:
			case K_SELECT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_135);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void relational_operator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case EQ:
			{
				match(EQ);
				break;
			}
			case SLASHEQ:
			{
				match(SLASHEQ);
				break;
			}
			case LST:
			{
				match(LST);
				break;
			}
			case LSTEQ:
			{
				match(LSTEQ);
				break;
			}
			case GRT:
			{
				match(GRT);
				break;
			}
			case GRTEQ:
			{
				match(GRTEQ);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_10);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void report_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_REPORT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_REPORT);
			expression();
			{
			switch ( LA(1)) {
			case K_SEVERITY:
			{
				match(K_SEVERITY);
				expression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void return_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_RETURN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_RETURN);
			{
			switch ( LA(1)) {
			case LPAREN:
			case PLUS:
			case MINUS:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case K_ABS:
			case K_NOT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			{
				expression();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void scalar_type_definition() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			if ((LA(1)==LPAREN)) {
				enumeration_type_definition();
			}
			else {
				boolean synPredMatched483 = false;
				if (((LA(1)==K_RANGE) && (_tokenSet_10.member(LA(2))))) {
					int _m483 = mark();
					synPredMatched483 = true;
					inputState.guessing++;
					try {
						{
						range_constraint();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched483 = false;
					}
					rewind(_m483);
inputState.guessing--;
				}
				if ( synPredMatched483 ) {
					range_constraint();
				}
				else if ((LA(1)==K_RANGE) && (_tokenSet_10.member(LA(2)))) {
					physical_type_definition();
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_1);
				} else {
				  throw ex;
				}
			}
		}
		
	public final void selected_waveforms() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			waveform();
			match(K_WHEN);
			choices();
			{
			_loop489:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					waveform();
					match(K_WHEN);
					choices();
				}
				else {
					break _loop489;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void sensitivity_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_ON);
			sensitivity_list();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_136);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void wait_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				break;
			}
			case K_WAIT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(K_WAIT);
			{
			switch ( LA(1)) {
			case K_ON:
			{
				sensitivity_clause();
				break;
			}
			case SEMI:
			case K_FOR:
			case K_UNTIL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_UNTIL:
			{
				condition_clause();
				break;
			}
			case SEMI:
			case K_FOR:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case K_FOR:
			{
				timeout_clause();
				break;
			}
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void variable_assignment_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
				label_colon();
			}
			else if ((_tokenSet_128.member(LA(1))) && (_tokenSet_137.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			target();
			match(COLONEQ);
			expression();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void signal_assignment_statement() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
				label_colon();
			}
			else if ((_tokenSet_128.member(LA(1))) && (_tokenSet_138.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			target();
			match(LSTEQ);
			{
			switch ( LA(1)) {
			case K_TRANSPORT:
			case K_REJECT:
			case K_INERTIAL:
			{
				delay_mechanism();
				break;
			}
			case LPAREN:
			case PLUS:
			case MINUS:
			case K_NEW:
			case BASED_LITERAL:
			case BIT_STRING_LITERAL:
			case CHARACTER_LITERAL:
			case DECIMAL_LITERAL:
			case K_ABS:
			case K_NOT:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case K_NULL:
			case STRING_LITERAL:
			case K_UNAFFECTED:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			waveform();
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void shift_operator() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_SLL:
			{
				match(K_SLL);
				break;
			}
			case K_SRL:
			{
				match(K_SRL);
				break;
			}
			case K_SLA:
			{
				match(K_SLA);
				break;
			}
			case K_SRA:
			{
				match(K_SRA);
				break;
			}
			case K_ROL:
			{
				match(K_ROL);
				break;
			}
			case K_ROR:
			{
				match(K_ROR);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_10);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void sign() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case PLUS:
			{
				match(PLUS);
				break;
			}
			case MINUS:
			{
				match(MINUS);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_12);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void signal_kind() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_REGISTER:
			{
				match(K_REGISTER);
				break;
			}
			case K_BUS:
			{
				match(K_BUS);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_139);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void term() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			factor();
			{
			_loop586:
			do {
				if (((LA(1) >= STAR && LA(1) <= K_REM)) && (_tokenSet_12.member(LA(2)))) {
					multiplying_operator();
					factor();
				}
				else {
					break _loop586;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subprogram_declarative_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop569:
			do {
				if ((_tokenSet_119.member(LA(1)))) {
					subprogram_declarative_item();
				}
				else {
					break _loop569;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subprogram_statement_part() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop577:
			do {
				if ((_tokenSet_62.member(LA(1)))) {
					sequential_statement();
				}
				else {
					break _loop577;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subprogram_kind() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			{
				match(K_PROCEDURE);
				break;
			}
			case K_FUNCTION:
			{
				match(K_FUNCTION);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_140);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void subprogram_declarative_item() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				break;
			}
			case K_FILE:
			{
				file_declaration();
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				break;
			}
			case K_USE:
			{
				use_clause();
				break;
			}
			default:
				boolean synPredMatched562 = false;
				if (((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2))))) {
					int _m562 = mark();
					synPredMatched562 = true;
					inputState.guessing++;
					try {
						{
						subprogram_declaration();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched562 = false;
					}
					rewind(_m562);
inputState.guessing--;
				}
				if ( synPredMatched562 ) {
					subprogram_declaration();
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
				}
				else {
					boolean synPredMatched564 = false;
					if (((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
						int _m564 = mark();
						synPredMatched564 = true;
						inputState.guessing++;
						try {
							{
							attribute_specification();
							}
						}
						catch (RecognitionException pe) {
							synPredMatched564 = false;
						}
						rewind(_m564);
inputState.guessing--;
					}
					if ( synPredMatched564 ) {
						attribute_specification();
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
					}
					else {
						boolean synPredMatched566 = false;
						if (((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER))) {
							int _m566 = mark();
							synPredMatched566 = true;
							inputState.guessing++;
							try {
								{
								match(K_GROUP);
								identifier();
								match(COLON);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched566 = false;
							}
							rewind(_m566);
inputState.guessing--;
						}
						if ( synPredMatched566 ) {
							group_declaration();
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
						}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					}}}
				}
				catch (RecognitionException ex) {
					if (inputState.guessing==0) {
						reportError(ex);
						recover(ex,_tokenSet_118);
					} else {
					  throw ex;
					}
				}
			}
			
	public final void timeout_clause() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(K_FOR);
			expression();
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void waveform_element() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			expression();
			{
			switch ( LA(1)) {
			case K_AFTER:
			{
				match(K_AFTER);
				expression();
				break;
			}
			case COMMA:
			case SEMI:
			case K_WHEN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_141);
			} else {
			  throw ex;
			}
		}
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"\"access\"",
		"\"open\"",
		"LPAREN",
		"RPAREN",
		"PLUS",
		"MINUS",
		"AND",
		"COMMA",
		"\"alias\"",
		"COLON",
		"\"is\"",
		"SEMI",
		"\"new\"",
		"\"architecture\"",
		"\"of\"",
		"\"begin\"",
		"\"end\"",
		"\"assert\"",
		"\"report\"",
		"\"severity\"",
		"EQGRT",
		"\"attribute\"",
		"TIC_SIMPLE_NAME",
		"BASED_LITERAL",
		"\"use\"",
		"BIT_STRING_LITERAL",
		"\"for\"",
		"\"group\"",
		"\"block\"",
		"\"case\"",
		"\"when\"",
		"CHARACTER_LITERAL",
		"\"others\"",
		"BAR",
		"\"component\"",
		"\"postponed\"",
		"\"until\"",
		"LSTEQ",
		"\"else\"",
		"\"configuration\"",
		"\"constant\"",
		"COLONEQ",
		"\"array\"",
		"DECIMAL_LITERAL",
		"\"transport\"",
		"\"reject\"",
		"\"inertial\"",
		"\"to\"",
		"\"downto\"",
		"\"disconnect\"",
		"\"after\"",
		"\"entity\"",
		"\"procedure\"",
		"\"type\"",
		"\"signal\"",
		"\"label\"",
		"\"function\"",
		"\"subtype\"",
		"\"variable\"",
		"\"literal\"",
		"\"package\"",
		"\"units\"",
		"LSTGRT",
		"\"all\"",
		"\"exit\"",
		"\"and\"",
		"\"or\"",
		"\"xor\"",
		"\"nand\"",
		"\"nor\"",
		"\"xnor\"",
		"STAR2",
		"\"abs\"",
		"\"not\"",
		"\"file\"",
		"\"generate\"",
		"\"if\"",
		"\"generic\"",
		"\"map\"",
		"BASIC_IDENTIFIER",
		"EXTENDED_IDENTIFIER",
		"\"then\"",
		"\"elsif\"",
		"\"range\"",
		"\"in\"",
		"\"bus\"",
		"\"while\"",
		"\"library\"",
		"\"body\"",
		"\"null\"",
		"\"loop\"",
		"\"out\"",
		"\"inout\"",
		"\"buffer\"",
		"\"linkage\"",
		"STAR",
		"SLASH",
		"\"mod\"",
		"\"rem\"",
		"DOT",
		"TIC",
		"\"next\"",
		"\"port\"",
		"\"process\"",
		"\"protected\"",
		"\"record\"",
		"EQ",
		"SLASHEQ",
		"LST",
		"GRT",
		"GRTEQ",
		"\"return\"",
		"\"with\"",
		"\"select\"",
		"\"on\"",
		"\"wait\"",
		"\"sll\"",
		"\"srl\"",
		"\"sla\"",
		"\"sra\"",
		"\"rol\"",
		"\"ror\"",
		"\"register\"",
		"LBRACK",
		"RBRACK",
		"STRING_LITERAL",
		"\"pure\"",
		"\"impure\"",
		"\"shared\"",
		"\"unaffected\"",
		"\"guarded\"",
		"QUOTE",
		"POUND",
		"USCORE",
		"EXCL",
		"DOLLAR",
		"PCNT",
		"AT",
		"QMARK",
		"BSLASH",
		"CARET",
		"BTIC",
		"LCURLY",
		"RCURLY",
		"TILDE",
		"WS",
		"NEWLINE",
		"COMMENT",
		"BASED_OR_DECIMAL",
		"BASE_SPECIFIER",
		"BASED_INTEGER",
		"EXTENDED_DIGIT",
		"BASIC_GRAPHIC_CHARACTER_BASE",
		"GRAPHIC_CHARACTER_BASE",
		"GRAPHIC_CHARACTER",
		"BIT_VALUE",
		"DIGIT",
		"EXPONENT",
		"LOWER_CASE_LETTER",
		"LETTER",
		"INTEGER"
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { 25937635021213602L, 9162503589648175074L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 32768L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = { 25937635021213602L, 9162503589646602210L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = { 2176L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = { 19144714729080962L, 9007200330612736L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = { 128L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = { 67108928L, -9223370387587334144L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = { 140772519248736L, 538456064L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = { 143040329093056L, -4681560016193830944L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = { 1251058606067019746L, -58610599533559830L, 15L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = { 140772519248704L, 538456064L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	private static final long[] mk_tokenSet_11() {
		long[] data = { 1250917833547771874L, -58611149826256926L, 15L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_11 = new BitSet(mk_tokenSet_11());
	private static final long[] mk_tokenSet_12() {
		long[] data = { 140772519247936L, 538456064L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_12 = new BitSet(mk_tokenSet_12());
	private static final long[] mk_tokenSet_13() {
		long[] data = { 1250917833547771874L, -58610600070443038L, 15L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_13 = new BitSet(mk_tokenSet_13());
	private static final long[] mk_tokenSet_14() {
		long[] data = { 140841238725440L, 538456064L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_14 = new BitSet(mk_tokenSet_14());
	private static final long[] mk_tokenSet_15() {
		long[] data = { 6896378202621760L, -9223369871644411904L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_15 = new BitSet(mk_tokenSet_15());
	private static final long[] mk_tokenSet_16() {
		long[] data = { 8583878760356909058L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_16 = new BitSet(mk_tokenSet_16());
	private static final long[] mk_tokenSet_17() {
		long[] data = { 24576L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_17 = new BitSet(mk_tokenSet_17());
	private static final long[] mk_tokenSet_18() {
		long[] data = { 67151872L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_18 = new BitSet(mk_tokenSet_18());
	private static final long[] mk_tokenSet_19() {
		long[] data = { 1250917833548034018L, -58610600053665822L, 15L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_19 = new BitSet(mk_tokenSet_19());
	private static final long[] mk_tokenSet_20() {
		long[] data = { 25937635088322530L, -60866797930770462L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_20 = new BitSet(mk_tokenSet_20());
	private static final long[] mk_tokenSet_21() {
		long[] data = { 36037593380552706L, 134217729L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_21 = new BitSet(mk_tokenSet_21());
	private static final long[] mk_tokenSet_22() {
		long[] data = { 8583878760355336192L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_22 = new BitSet(mk_tokenSet_22());
	private static final long[] mk_tokenSet_23() {
		long[] data = { 524288L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_23 = new BitSet(mk_tokenSet_23());
	private static final long[] mk_tokenSet_24() {
		long[] data = { 549757911104L, 4512395721965568L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_24 = new BitSet(mk_tokenSet_24());
	private static final long[] mk_tokenSet_25() {
		long[] data = { 1048576L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_25 = new BitSet(mk_tokenSet_25());
	private static final long[] mk_tokenSet_26() {
		long[] data = { 1250917833548034018L, -58610600070443038L, 15L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_26 = new BitSet(mk_tokenSet_26());
	private static final long[] mk_tokenSet_27() {
		long[] data = { 1224979098644774912L, 0L, 12L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_27 = new BitSet(mk_tokenSet_27());
	private static final long[] mk_tokenSet_28() {
		long[] data = { 1152921504606846976L, 1572864L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_28 = new BitSet(mk_tokenSet_28());
	private static final long[] mk_tokenSet_29() {
		long[] data = { 8583878760355860480L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_29 = new BitSet(mk_tokenSet_29());
	private static final long[] mk_tokenSet_30() {
		long[] data = { 549755813888L, 8796094595072L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_30 = new BitSet(mk_tokenSet_30());
	private static final long[] mk_tokenSet_31() {
		long[] data = { 8286640908997783616L, 8796093038592L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_31 = new BitSet(mk_tokenSet_31());
	private static final long[] mk_tokenSet_32() {
		long[] data = { 549755813888L, 1572864L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_32 = new BitSet(mk_tokenSet_32());
	private static final long[] mk_tokenSet_33() {
		long[] data = { 67149888L, -9223370387585761280L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_33 = new BitSet(mk_tokenSet_33());
	private static final long[] mk_tokenSet_34() {
		long[] data = { 549757911040L, 1572864L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_34 = new BitSet(mk_tokenSet_34());
	private static final long[] mk_tokenSet_35() {
		long[] data = { 140772521354048L, 538456064L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_35 = new BitSet(mk_tokenSet_35());
	private static final long[] mk_tokenSet_36() {
		long[] data = { 549755813952L, 4503599628943360L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_36 = new BitSet(mk_tokenSet_36());
	private static final long[] mk_tokenSet_37() {
		long[] data = { 143040329098048L, -9218866787421507584L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_37 = new BitSet(mk_tokenSet_37());
	private static final long[] mk_tokenSet_38() {
		long[] data = { 549758959680L, 4512395721965568L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_38 = new BitSet(mk_tokenSet_38());
	private static final long[] mk_tokenSet_39() {
		long[] data = { 4399132868608L, 1075871744L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_39 = new BitSet(mk_tokenSet_39());
	private static final long[] mk_tokenSet_40() {
		long[] data = { 4424897396800L, 38282797539459088L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_40 = new BitSet(mk_tokenSet_40());
	private static final long[] mk_tokenSet_41() {
		long[] data = { 559425781824L, 42795193255657488L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_41 = new BitSet(mk_tokenSet_41());
	private static final long[] mk_tokenSet_42() {
		long[] data = { 83886144L, -9223370387587334144L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_42 = new BitSet(mk_tokenSet_42());
	private static final long[] mk_tokenSet_43() {
		long[] data = { 16777216L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_43 = new BitSet(mk_tokenSet_43());
	private static final long[] mk_tokenSet_44() {
		long[] data = { 262144L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_44 = new BitSet(mk_tokenSet_44());
	private static final long[] mk_tokenSet_45() {
		long[] data = { 8583878760356909056L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_45 = new BitSet(mk_tokenSet_45());
	private static final long[] mk_tokenSet_46() {
		long[] data = { 16384L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_46 = new BitSet(mk_tokenSet_46());
	private static final long[] mk_tokenSet_47() {
		long[] data = { 1048576L, 1572864L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_47 = new BitSet(mk_tokenSet_47());
	private static final long[] mk_tokenSet_48() {
		long[] data = { 32768L, 4398046642176L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_48 = new BitSet(mk_tokenSet_48());
	private static final long[] mk_tokenSet_49() {
		long[] data = { 32768L, 4398046511104L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_49 = new BitSet(mk_tokenSet_49());
	private static final long[] mk_tokenSet_50() {
		long[] data = { 1074790400L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_50 = new BitSet(mk_tokenSet_50());
	private static final long[] mk_tokenSet_51() {
		long[] data = { 1410334784L, -9223370387587334144L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_51 = new BitSet(mk_tokenSet_51());
	private static final long[] mk_tokenSet_52() {
		long[] data = { 1343225856L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_52 = new BitSet(mk_tokenSet_52());
	private static final long[] mk_tokenSet_53() {
		long[] data = { 8619916353469026304L, 134234113L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_53 = new BitSet(mk_tokenSet_53());
	private static final long[] mk_tokenSet_54() {
		long[] data = { 68719476736L, 1572872L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_54 = new BitSet(mk_tokenSet_54());
	private static final long[] mk_tokenSet_55() {
		long[] data = { 8583878760356909056L, 4398046658560L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_55 = new BitSet(mk_tokenSet_55());
	private static final long[] mk_tokenSet_56() {
		long[] data = { 8583878760356909056L, 4398046527488L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_56 = new BitSet(mk_tokenSet_56());
	private static final long[] mk_tokenSet_57() {
		long[] data = { 17179912256L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_57 = new BitSet(mk_tokenSet_57());
	private static final long[] mk_tokenSet_58() {
		long[] data = { 6896240746891200L, -9223369871644411904L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_58 = new BitSet(mk_tokenSet_58());
	private static final long[] mk_tokenSet_59() {
		long[] data = { 143040329091008L, -4681560016193830944L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_59 = new BitSet(mk_tokenSet_59());
	private static final long[] mk_tokenSet_60() {
		long[] data = { 17180917760L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_60 = new BitSet(mk_tokenSet_60());
	private static final long[] mk_tokenSet_61() {
		long[] data = { 16812032L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_61 = new BitSet(mk_tokenSet_61());
	private static final long[] mk_tokenSet_62() {
		long[] data = { 9669967936L, 38282797535264784L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_62 = new BitSet(mk_tokenSet_62());
	private static final long[] mk_tokenSet_63() {
		long[] data = { 4415227428864L, 4194304L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_63 = new BitSet(mk_tokenSet_63());
	private static final long[] mk_tokenSet_64() {
		long[] data = { 140978761600832L, -9223369871652800512L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_64 = new BitSet(mk_tokenSet_64());
	private static final long[] mk_tokenSet_65() {
		long[] data = { 137455765504L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_65 = new BitSet(mk_tokenSet_65());
	private static final long[] mk_tokenSet_66() {
		long[] data = { 6896378202656576L, -9223369871644411904L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_66 = new BitSet(mk_tokenSet_66());
	private static final long[] mk_tokenSet_67() {
		long[] data = { 6896378202656704L, -9223369870579025920L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_67 = new BitSet(mk_tokenSet_67());
	private static final long[] mk_tokenSet_68() {
		long[] data = { 137522874560L, -9223370386503598080L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_68 = new BitSet(mk_tokenSet_68());
	private static final long[] mk_tokenSet_69() {
		long[] data = { 137455765632L, 1073774592L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_69 = new BitSet(mk_tokenSet_69());
	private static final long[] mk_tokenSet_70() {
		long[] data = { 1343258624L, 4398046642176L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_70 = new BitSet(mk_tokenSet_70());
	private static final long[] mk_tokenSet_71() {
		long[] data = { 8192L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_71 = new BitSet(mk_tokenSet_71());
	private static final long[] mk_tokenSet_72() {
		long[] data = { 67141696L, -9223370387585761280L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_72 = new BitSet(mk_tokenSet_72());
	private static final long[] mk_tokenSet_73() {
		long[] data = { 143040329089856L, -9218866787421507584L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_73 = new BitSet(mk_tokenSet_73());
	private static final long[] mk_tokenSet_74() {
		long[] data = { 1073774592L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_74 = new BitSet(mk_tokenSet_74());
	private static final long[] mk_tokenSet_75() {
		long[] data = { 37383395344384L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_75 = new BitSet(mk_tokenSet_75());
	private static final long[] mk_tokenSet_76() {
		long[] data = { 140772519248704L, 538456064L, 34L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_76 = new BitSet(mk_tokenSet_76());
	private static final long[] mk_tokenSet_77() {
		long[] data = { 141322278208320L, 4512396258848768L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_77 = new BitSet(mk_tokenSet_77());
	private static final long[] mk_tokenSet_78() {
		long[] data = { 17179901952L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_78 = new BitSet(mk_tokenSet_78());
	private static final long[] mk_tokenSet_79() {
		long[] data = { 1073741824L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_79 = new BitSet(mk_tokenSet_79());
	private static final long[] mk_tokenSet_80() {
		long[] data = { 3523215360L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_80 = new BitSet(mk_tokenSet_80());
	private static final long[] mk_tokenSet_81() {
		long[] data = { 25937635021475746L, 9162503589646602210L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_81 = new BitSet(mk_tokenSet_81());
	private static final long[] mk_tokenSet_82() {
		long[] data = { 36037593112117248L, 1L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_82 = new BitSet(mk_tokenSet_82());
	private static final long[] mk_tokenSet_83() {
		long[] data = { 36037593380552704L, 134217729L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_83 = new BitSet(mk_tokenSet_83());
	private static final long[] mk_tokenSet_84() {
		long[] data = { 4899933986765144064L, 16384L, 16L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_84 = new BitSet(mk_tokenSet_84());
	private static final long[] mk_tokenSet_85() {
		long[] data = { 4899933986765144064L, 1589248L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_85 = new BitSet(mk_tokenSet_85());
	private static final long[] mk_tokenSet_86() {
		long[] data = { 10240L, 1572864L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_86 = new BitSet(mk_tokenSet_86());
	private static final long[] mk_tokenSet_87() {
		long[] data = { 2L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_87 = new BitSet(mk_tokenSet_87());
	private static final long[] mk_tokenSet_88() {
		long[] data = { 32898L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_88 = new BitSet(mk_tokenSet_88());
	private static final long[] mk_tokenSet_89() {
		long[] data = { 1224979098947862592L, 2251799813685248L, 12L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_89 = new BitSet(mk_tokenSet_89());
	private static final long[] mk_tokenSet_90() {
		long[] data = { 18014398509481984L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_90 = new BitSet(mk_tokenSet_90());
	private static final long[] mk_tokenSet_91() {
		long[] data = { 6896240746891072L, -9223369871652800512L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_91 = new BitSet(mk_tokenSet_91());
	private static final long[] mk_tokenSet_92() {
		long[] data = { 25937635088322530L, -60866797940731934L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_92 = new BitSet(mk_tokenSet_92());
	private static final long[] mk_tokenSet_93() {
		long[] data = { 18560L, 4L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_93 = new BitSet(mk_tokenSet_93());
	private static final long[] mk_tokenSet_94() {
		long[] data = { 8583878484405260288L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_94 = new BitSet(mk_tokenSet_94());
	private static final long[] mk_tokenSet_95() {
		long[] data = { 8583878484403687424L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_95 = new BitSet(mk_tokenSet_95());
	private static final long[] mk_tokenSet_96() {
		long[] data = { 1572864L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_96 = new BitSet(mk_tokenSet_96());
	private static final long[] mk_tokenSet_97() {
		long[] data = { 549757911040L, 8796094595072L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_97 = new BitSet(mk_tokenSet_97());
	private static final long[] mk_tokenSet_98() {
		long[] data = { 10240L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_98 = new BitSet(mk_tokenSet_98());
	private static final long[] mk_tokenSet_99() {
		long[] data = { 10240L, -9223372036854775808L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_99 = new BitSet(mk_tokenSet_99());
	private static final long[] mk_tokenSet_100() {
		long[] data = { 549758959616L, 8796094595072L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_100 = new BitSet(mk_tokenSet_100());
	private static final long[] mk_tokenSet_101() {
		long[] data = { 19144714729080962L, 9007200330614752L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_101 = new BitSet(mk_tokenSet_101());
	private static final long[] mk_tokenSet_102() {
		long[] data = { 140772519247936L, 538443776L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_102 = new BitSet(mk_tokenSet_102());
	private static final long[] mk_tokenSet_103() {
		long[] data = { 8609958893469958114L, -18067207699562510L, 63L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_103 = new BitSet(mk_tokenSet_103());
	private static final long[] mk_tokenSet_104() {
		long[] data = { 140772519182336L, 538443776L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_104 = new BitSet(mk_tokenSet_104());
	private static final long[] mk_tokenSet_105() {
		long[] data = { 25937635088322530L, -60866797939159070L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_105 = new BitSet(mk_tokenSet_105());
	private static final long[] mk_tokenSet_106() {
		long[] data = { 0L, 32768L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_106 = new BitSet(mk_tokenSet_106());
	private static final long[] mk_tokenSet_107() {
		long[] data = { 0L, 1073774592L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_107 = new BitSet(mk_tokenSet_107());
	private static final long[] mk_tokenSet_108() {
		long[] data = { 32896L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_108 = new BitSet(mk_tokenSet_108());
	private static final long[] mk_tokenSet_109() {
		long[] data = { 0L, 1572864L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_109 = new BitSet(mk_tokenSet_109());
	private static final long[] mk_tokenSet_110() {
		long[] data = { 0L, 1073741824L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_110 = new BitSet(mk_tokenSet_110());
	private static final long[] mk_tokenSet_111() {
		long[] data = { 140737622573056L, 1572864L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_111 = new BitSet(mk_tokenSet_111());
	private static final long[] mk_tokenSet_112() {
		long[] data = { 34816L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_112 = new BitSet(mk_tokenSet_112());
	private static final long[] mk_tokenSet_113() {
		long[] data = { 8286640908963680256L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_113 = new BitSet(mk_tokenSet_113());
	private static final long[] mk_tokenSet_114() {
		long[] data = { 8286640908964728832L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_114 = new BitSet(mk_tokenSet_114());
	private static final long[] mk_tokenSet_115() {
		long[] data = { 8583878759281594368L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_115 = new BitSet(mk_tokenSet_115());
	private static final long[] mk_tokenSet_116() {
		long[] data = { 8583878759282642944L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_116 = new BitSet(mk_tokenSet_116());
	private static final long[] mk_tokenSet_117() {
		long[] data = { 67141696L, -9223370387587334144L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_117 = new BitSet(mk_tokenSet_117());
	private static final long[] mk_tokenSet_118() {
		long[] data = { 8286640908997758976L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_118 = new BitSet(mk_tokenSet_118());
	private static final long[] mk_tokenSet_119() {
		long[] data = { 8286640908997234688L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_119 = new BitSet(mk_tokenSet_119());
	private static final long[] mk_tokenSet_120() {
		long[] data = { 1100585402496L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_120 = new BitSet(mk_tokenSet_120());
	private static final long[] mk_tokenSet_121() {
		long[] data = { 1100585410560L, 18014398509481984L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_121 = new BitSet(mk_tokenSet_121());
	private static final long[] mk_tokenSet_122() {
		long[] data = { 140772519256896L, 538456064L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_122 = new BitSet(mk_tokenSet_122());
	private static final long[] mk_tokenSet_123() {
		long[] data = { 17179910144L, 1572864L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_123 = new BitSet(mk_tokenSet_123());
	private static final long[] mk_tokenSet_124() {
		long[] data = { 140772519289664L, 538456064L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_124 = new BitSet(mk_tokenSet_124());
	private static final long[] mk_tokenSet_125() {
		long[] data = { 1073741824L, 1142423552L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_125 = new BitSet(mk_tokenSet_125());
	private static final long[] mk_tokenSet_126() {
		long[] data = { 140782190273344L, 38282797535277072L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_126 = new BitSet(mk_tokenSet_126());
	private static final long[] mk_tokenSet_127() {
		long[] data = { 67149888L, -9223370387587334144L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_127 = new BitSet(mk_tokenSet_127());
	private static final long[] mk_tokenSet_128() {
		long[] data = { 64L, 1572864L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_128 = new BitSet(mk_tokenSet_128());
	private static final long[] mk_tokenSet_129() {
		long[] data = { 176025677931328L, -9223370387048878080L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_129 = new BitSet(mk_tokenSet_129());
	private static final long[] mk_tokenSet_130() {
		long[] data = { 143040329098048L, -9223370387048878080L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_130 = new BitSet(mk_tokenSet_130());
	private static final long[] mk_tokenSet_131() {
		long[] data = { 8286640908998283264L, 16384L, 28L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_131 = new BitSet(mk_tokenSet_131());
	private static final long[] mk_tokenSet_132() {
		long[] data = { 1224979098946764800L, 0L, 12L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_132 = new BitSet(mk_tokenSet_132());
	private static final long[] mk_tokenSet_133() {
		long[] data = { 1224979098947813376L, 0L, 12L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_133 = new BitSet(mk_tokenSet_133());
	private static final long[] mk_tokenSet_134() {
		long[] data = { 1224979098947862528L, 0L, 12L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_134 = new BitSet(mk_tokenSet_134());
	private static final long[] mk_tokenSet_135() {
		long[] data = { 19146913752336514L, 11188631400122336L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_135 = new BitSet(mk_tokenSet_135());
	private static final long[] mk_tokenSet_136() {
		long[] data = { 1100585402368L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_136 = new BitSet(mk_tokenSet_136());
	private static final long[] mk_tokenSet_137() {
		long[] data = { 176025677923136L, -9223370387048878080L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_137 = new BitSet(mk_tokenSet_137());
	private static final long[] mk_tokenSet_138() {
		long[] data = { 143040329089856L, -9223370387048878080L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_138 = new BitSet(mk_tokenSet_138());
	private static final long[] mk_tokenSet_139() {
		long[] data = { 35184372121600L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_139 = new BitSet(mk_tokenSet_139());
	private static final long[] mk_tokenSet_140() {
		long[] data = { 32768L, 1572864L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_140 = new BitSet(mk_tokenSet_140());
	private static final long[] mk_tokenSet_141() {
		long[] data = { 17179904000L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_141 = new BitSet(mk_tokenSet_141());
	
	}

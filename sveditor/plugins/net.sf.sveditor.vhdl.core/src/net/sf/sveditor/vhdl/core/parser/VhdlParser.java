// $ANTLR 2.7.7 (2006-11-01): "vhdl.g" -> "VhdlParser.java"$

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
import antlr.collections.AST;
import java.util.Hashtable;
import antlr.ASTFactory;
import antlr.ASTPair;
import antlr.collections.impl.ASTArray;

public class VhdlParser extends antlr.LLkParser       implements VhdlParserTokenTypes
 {

	/**
	 *	Track module declarations and instances.
	 */
	public Tracker			stTracker = new Tracker();

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
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
}

public VhdlParser(TokenBuffer tokenBuf) {
  this(tokenBuf,2);
}

protected VhdlParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
}

public VhdlParser(TokenStream lexer) {
  this(lexer,2);
}

public VhdlParser(ParserSharedInputState state) {
  super(state,2);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
}

	public final void abstract_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST abstract_literal_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case DECIMAL_LITERAL:
			{
				decimal_literal();
				astFactory.addASTChild(currentAST, returnAST);
				abstract_literal_AST = (AST)currentAST.root;
				break;
			}
			case BASED_LITERAL:
			{
				based_literal();
				astFactory.addASTChild(currentAST, returnAST);
				abstract_literal_AST = (AST)currentAST.root;
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
		returnAST = abstract_literal_AST;
	}
	
	public final void decimal_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST decimal_literal_AST = null;
		
		try {      // for error handling
			AST tmp1_AST = null;
			tmp1_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp1_AST);
			match(DECIMAL_LITERAL);
			decimal_literal_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		returnAST = decimal_literal_AST;
	}
	
	public final void based_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST based_literal_AST = null;
		
		try {      // for error handling
			AST tmp2_AST = null;
			tmp2_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp2_AST);
			match(BASED_LITERAL);
			based_literal_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		returnAST = based_literal_AST;
	}
	
	public final void access_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST access_type_definition_AST = null;
		
		try {      // for error handling
			AST tmp3_AST = null;
			tmp3_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp3_AST);
			match(K_ACCESS);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			access_type_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = access_type_definition_AST;
	}
	
	public final void subtype_indication() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subtype_indication_AST = null;
		
		try {      // for error handling
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			subtype_indication_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = subtype_indication_AST;
	}
	
	public final void actual_designator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST actual_designator_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				actual_designator_AST = (AST)currentAST.root;
				break;
			}
			case K_OPEN:
			{
				AST tmp4_AST = null;
				tmp4_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp4_AST);
				match(K_OPEN);
				actual_designator_AST = (AST)currentAST.root;
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
		returnAST = actual_designator_AST;
	}
	
	public final void expression() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expression_AST = null;
		
		try {      // for error handling
			relation();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop245:
			do {
				if (((LA(1) >= K_AND && LA(1) <= K_XNOR))) {
					logical_op();
					astFactory.addASTChild(currentAST, returnAST);
					relation();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop245;
				}
				
			} while (true);
			}
			expression_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = expression_AST;
	}
	
	public final void actual_parameter_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST actual_parameter_part_AST = null;
		
		try {      // for error handling
			association_list();
			astFactory.addASTChild(currentAST, returnAST);
			actual_parameter_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = actual_parameter_part_AST;
	}
	
	public final void association_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST association_list_AST = null;
		
		try {      // for error handling
			association_element();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop43:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp5_AST = null;
					tmp5_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp5_AST);
					match(COMMA);
					association_element();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop43;
				}
				
			} while (true);
			}
			association_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = association_list_AST;
	}
	
	public final void actual_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST actual_part_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp6_AST = null;
				tmp6_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp6_AST);
				match(LPAREN);
				actual_designator();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp7_AST = null;
				tmp7_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp7_AST);
				match(RPAREN);
				actual_part_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_7.member(LA(1))) && (_tokenSet_8.member(LA(2)))) {
				actual_designator();
				astFactory.addASTChild(currentAST, returnAST);
				actual_part_AST = (AST)currentAST.root;
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
		returnAST = actual_part_AST;
	}
	
	public final Token  name() throws RecognitionException, TokenStreamException {
		Token tok;
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST name_AST = null;
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
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					smplName = new StringBuilder(tok.getText()); first=tok;
				}
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				astFactory.addASTChild(currentAST, returnAST);
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
						AST tmp8_AST = null;
						tmp8_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp8_AST);
						match(DOT);
						tok=suffix();
						astFactory.addASTChild(currentAST, returnAST);
						if ( inputState.guessing==0 ) {
								if ((tok != null) && (null != smplName)) {
													smplName.append('.').append(tok.getText());
												}
											
						}
						break;
					}
					case TIC:
					{
						AST tmp9_AST = null;
						tmp9_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp9_AST);
						match(TIC);
						aggregate();
						astFactory.addASTChild(currentAST, returnAST);
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
							astFactory.addASTChild(currentAST, returnAST);
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
						astFactory.addASTChild(currentAST, returnAST);
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
							AST tmp10_AST = null;
							tmp10_AST = astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp10_AST);
							match(LPAREN);
							expression();
							astFactory.addASTChild(currentAST, returnAST);
							{
							_loop359:
							do {
								if ((LA(1)==COMMA)) {
									AST tmp11_AST = null;
									tmp11_AST = astFactory.create(LT(1));
									astFactory.addASTChild(currentAST, tmp11_AST);
									match(COMMA);
									expression();
									astFactory.addASTChild(currentAST, returnAST);
								}
								else {
									break _loop359;
								}
								
							} while (true);
							}
							AST tmp12_AST = null;
							tmp12_AST = astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp12_AST);
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
								AST tmp13_AST = null;
								tmp13_AST = astFactory.create(LT(1));
								astFactory.addASTChild(currentAST, tmp13_AST);
								match(LPAREN);
								actual_parameter_part();
								astFactory.addASTChild(currentAST, returnAST);
								AST tmp14_AST = null;
								tmp14_AST = astFactory.create(LT(1));
								astFactory.addASTChild(currentAST, tmp14_AST);
								match(RPAREN);
							}
							else if ((LA(1)==LPAREN) && (_tokenSet_10.member(LA(2)))) {
								AST tmp15_AST = null;
								tmp15_AST = astFactory.create(LT(1));
								astFactory.addASTChild(currentAST, tmp15_AST);
								match(LPAREN);
								discrete_range();
								astFactory.addASTChild(currentAST, returnAST);
								AST tmp16_AST = null;
								tmp16_AST = astFactory.create(LT(1));
								astFactory.addASTChild(currentAST, tmp16_AST);
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
				name_AST = (AST)currentAST.root;
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_11);
				} else {
				  throw ex;
				}
			}
			returnAST = name_AST;
			return tok;
		}
		
	public final void adding_operator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST adding_operator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case PLUS:
			{
				AST tmp17_AST = null;
				tmp17_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp17_AST);
				match(PLUS);
				adding_operator_AST = (AST)currentAST.root;
				break;
			}
			case MINUS:
			{
				AST tmp18_AST = null;
				tmp18_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp18_AST);
				match(MINUS);
				adding_operator_AST = (AST)currentAST.root;
				break;
			}
			case AND:
			{
				AST tmp19_AST = null;
				tmp19_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp19_AST);
				match(AND);
				adding_operator_AST = (AST)currentAST.root;
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
		returnAST = adding_operator_AST;
	}
	
	public final void aggregate() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST aggregate_AST = null;
		
		try {      // for error handling
			AST tmp20_AST = null;
			tmp20_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp20_AST);
			match(LPAREN);
			element_association();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop11:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp21_AST = null;
					tmp21_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp21_AST);
					match(COMMA);
					element_association();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop11;
				}
				
			} while (true);
			}
			AST tmp22_AST = null;
			tmp22_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp22_AST);
			match(RPAREN);
			aggregate_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		returnAST = aggregate_AST;
	}
	
	public final void element_association() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST element_association_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp23_AST = null;
				tmp23_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp23_AST);
				match(EQGRT);
			}
			else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_8.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			element_association_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
		returnAST = element_association_AST;
	}
	
	public final void alias_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST alias_declaration_AST = null;
		
		try {      // for error handling
			AST tmp24_AST = null;
			tmp24_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp24_AST);
			match(K_ALIAS);
			alias_designator();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case COLON:
			{
				AST tmp25_AST = null;
				tmp25_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp25_AST);
				match(COLON);
				subtype_indication();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp26_AST = null;
			tmp26_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp26_AST);
			match(K_IS);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LBRACK:
			{
				signature();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp27_AST = null;
			tmp27_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp27_AST);
			match(SEMI);
			alias_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = alias_declaration_AST;
	}
	
	public final void alias_designator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST alias_designator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				identifier();
				astFactory.addASTChild(currentAST, returnAST);
				alias_designator_AST = (AST)currentAST.root;
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				astFactory.addASTChild(currentAST, returnAST);
				alias_designator_AST = (AST)currentAST.root;
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				astFactory.addASTChild(currentAST, returnAST);
				alias_designator_AST = (AST)currentAST.root;
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
		returnAST = alias_designator_AST;
	}
	
	public final void signature() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signature_AST = null;
		
		try {      // for error handling
			AST tmp28_AST = null;
			tmp28_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp28_AST);
			match(LBRACK);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				astFactory.addASTChild(currentAST, returnAST);
				{
				_loop548:
				do {
					if ((LA(1)==COMMA)) {
						AST tmp29_AST = null;
						tmp29_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp29_AST);
						match(COMMA);
						name();
						astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp30_AST = null;
				tmp30_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp30_AST);
				match(K_RETURN);
				name();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp31_AST = null;
			tmp31_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp31_AST);
			match(RBRACK);
			signature_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_18);
			} else {
			  throw ex;
			}
		}
		returnAST = signature_AST;
	}
	
	public final Token  identifier() throws RecognitionException, TokenStreamException {
		Token tok;
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST identifier_AST = null;
		Token  id = null;
		AST id_AST = null;
		Token  id2 = null;
		AST id2_AST = null;
		tok=null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			{
				id = LT(1);
				id_AST = astFactory.create(id);
				astFactory.addASTChild(currentAST, id_AST);
				match(BASIC_IDENTIFIER);
				if ( inputState.guessing==0 ) {
					tok=id;
				}
				identifier_AST = (AST)currentAST.root;
				break;
			}
			case EXTENDED_IDENTIFIER:
			{
				id2 = LT(1);
				id2_AST = astFactory.create(id2);
				astFactory.addASTChild(currentAST, id2_AST);
				match(EXTENDED_IDENTIFIER);
				if ( inputState.guessing==0 ) {
					tok=id2;
				}
				identifier_AST = (AST)currentAST.root;
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
		returnAST = identifier_AST;
		return tok;
	}
	
	public final void character_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST character_literal_AST = null;
		
		try {      // for error handling
			AST tmp32_AST = null;
			tmp32_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp32_AST);
			match(CHARACTER_LITERAL);
			character_literal_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		returnAST = character_literal_AST;
	}
	
	public final void operator_symbol() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST operator_symbol_AST = null;
		
		try {      // for error handling
			string_literal();
			astFactory.addASTChild(currentAST, returnAST);
			operator_symbol_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		returnAST = operator_symbol_AST;
	}
	
	public final void allocator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST allocator_AST = null;
		
		try {      // for error handling
			AST tmp33_AST = null;
			tmp33_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp33_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_6.member(LA(2)))) {
				qualified_expression();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			allocator_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = allocator_AST;
	}
	
	public final void qualified_expression() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST qualified_expression_AST = null;
		
		try {      // for error handling
			name();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp34_AST = null;
			tmp34_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp34_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((LA(1)==LPAREN) && (_tokenSet_10.member(LA(2)))) {
				AST tmp35_AST = null;
				tmp35_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp35_AST);
				match(LPAREN);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp36_AST = null;
				tmp36_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp36_AST);
				match(RPAREN);
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			qualified_expression_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = qualified_expression_AST;
	}
	
	public final void architecture_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST architecture_body_AST = null;
		
		try {      // for error handling
			AST tmp37_AST = null;
			tmp37_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp37_AST);
			match(K_ARCHITECTURE);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp38_AST = null;
			tmp38_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp38_AST);
			match(K_OF);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp39_AST = null;
			tmp39_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp39_AST);
			match(K_IS);
			architecture_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp40_AST = null;
			tmp40_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp40_AST);
			match(K_BEGIN);
			architecture_statement_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp41_AST = null;
			tmp41_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp41_AST);
			match(K_END);
			{
			switch ( LA(1)) {
			case K_ARCHITECTURE:
			{
				AST tmp42_AST = null;
				tmp42_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp42_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp43_AST = null;
			tmp43_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp43_AST);
			match(SEMI);
			architecture_body_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		returnAST = architecture_body_AST;
	}
	
	public final void architecture_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST architecture_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop25:
			do {
				if ((_tokenSet_22.member(LA(1)))) {
					block_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop25;
				}
				
			} while (true);
			}
			architecture_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
		returnAST = architecture_declarative_part_AST;
	}
	
	public final void architecture_statement_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST architecture_statement_part_AST = null;
		
		try {      // for error handling
			{
			_loop28:
			do {
				if ((_tokenSet_24.member(LA(1)))) {
					concurrent_statement();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop28;
				}
				
			} while (true);
			}
			architecture_statement_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = architecture_statement_part_AST;
	}
	
	public final Token  simple_name() throws RecognitionException, TokenStreamException {
		Token tok;
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST simple_name_AST = null;
		tok=null;
		
		try {      // for error handling
			tok=identifier();
			astFactory.addASTChild(currentAST, returnAST);
			simple_name_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_26);
			} else {
			  throw ex;
			}
		}
		returnAST = simple_name_AST;
		return tok;
	}
	
	public final void block_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST block_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_COMPONENT:
			{
				component_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FOR:
			{
				configuration_specification();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_DISCONNECT:
			{
				disconnection_specification();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				block_declarative_item_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					block_declarative_item_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
					astFactory.addASTChild(currentAST, returnAST);
					block_declarative_item_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						block_declarative_item_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						block_declarative_item_AST = (AST)currentAST.root;
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
							astFactory.addASTChild(currentAST, returnAST);
							block_declarative_item_AST = (AST)currentAST.root;
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
							astFactory.addASTChild(currentAST, returnAST);
							block_declarative_item_AST = (AST)currentAST.root;
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
				returnAST = block_declarative_item_AST;
			}
			
	public final void concurrent_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST concurrent_statement_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				concurrent_statement_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					concurrent_statement_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						concurrent_statement_AST = (AST)currentAST.root;
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
							astFactory.addASTChild(currentAST, returnAST);
							concurrent_statement_AST = (AST)currentAST.root;
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
								astFactory.addASTChild(currentAST, returnAST);
								concurrent_statement_AST = (AST)currentAST.root;
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
									astFactory.addASTChild(currentAST, returnAST);
									concurrent_statement_AST = (AST)currentAST.root;
								}
								else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
									generate_statement();
									astFactory.addASTChild(currentAST, returnAST);
									concurrent_statement_AST = (AST)currentAST.root;
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
							returnAST = concurrent_statement_AST;
						}
						
	public final void array_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST array_type_definition_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				array_type_definition_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==K_ARRAY) && (LA(2)==LPAREN)) {
				constrained_array_definition();
				astFactory.addASTChild(currentAST, returnAST);
				array_type_definition_AST = (AST)currentAST.root;
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
		returnAST = array_type_definition_AST;
	}
	
	public final void unconstrained_array_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST unconstrained_array_definition_AST = null;
		
		try {      // for error handling
			AST tmp44_AST = null;
			tmp44_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp44_AST);
			match(K_ARRAY);
			AST tmp45_AST = null;
			tmp45_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp45_AST);
			match(LPAREN);
			index_subtype_definition();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop594:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp46_AST = null;
					tmp46_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp46_AST);
					match(COMMA);
					index_subtype_definition();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop594;
				}
				
			} while (true);
			}
			AST tmp47_AST = null;
			tmp47_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp47_AST);
			match(RPAREN);
			AST tmp48_AST = null;
			tmp48_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp48_AST);
			match(K_OF);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			unconstrained_array_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = unconstrained_array_definition_AST;
	}
	
	public final void constrained_array_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST constrained_array_definition_AST = null;
		
		try {      // for error handling
			AST tmp49_AST = null;
			tmp49_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp49_AST);
			match(K_ARRAY);
			index_constraint();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp50_AST = null;
			tmp50_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp50_AST);
			match(K_OF);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			constrained_array_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = constrained_array_definition_AST;
	}
	
	public final void assertion() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assertion_AST = null;
		
		try {      // for error handling
			AST tmp51_AST = null;
			tmp51_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp51_AST);
			match(K_ASSERT);
			condition();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_REPORT:
			{
				AST tmp52_AST = null;
				tmp52_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp52_AST);
				match(K_REPORT);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp53_AST = null;
				tmp53_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp53_AST);
				match(K_SEVERITY);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			assertion_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = assertion_AST;
	}
	
	public final void condition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST condition_AST = null;
		
		try {      // for error handling
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			condition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_39);
			} else {
			  throw ex;
			}
		}
		returnAST = condition_AST;
	}
	
	public final void assertion_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assertion_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp54_AST = null;
			tmp54_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp54_AST);
			match(SEMI);
			assertion_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = assertion_statement_AST;
	}
	
	public final void label_colon() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST label_colon_AST = null;
		
		try {      // for error handling
			label();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp55_AST = null;
			tmp55_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp55_AST);
			match(COLON);
			label_colon_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_41);
			} else {
			  throw ex;
			}
		}
		returnAST = label_colon_AST;
	}
	
	public final void association_element() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST association_element_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp56_AST = null;
				tmp56_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp56_AST);
				match(EQGRT);
			}
			else if ((_tokenSet_7.member(LA(1))) && (_tokenSet_8.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			actual_part();
			astFactory.addASTChild(currentAST, returnAST);
			association_element_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
		returnAST = association_element_AST;
	}
	
	public final void formal_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST formal_part_AST = null;
		
		try {      // for error handling
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				AST tmp57_AST = null;
				tmp57_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp57_AST);
				match(LPAREN);
				name();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp58_AST = null;
				tmp58_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp58_AST);
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
			formal_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_43);
			} else {
			  throw ex;
			}
		}
		returnAST = formal_part_AST;
	}
	
	public final void attribute_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST attribute_declaration_AST = null;
		
		try {      // for error handling
			AST tmp59_AST = null;
			tmp59_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp59_AST);
			match(K_ATTRIBUTE);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp60_AST = null;
			tmp60_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp60_AST);
			match(COLON);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp61_AST = null;
			tmp61_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp61_AST);
			match(SEMI);
			attribute_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = attribute_declaration_AST;
	}
	
	public final void attribute_designator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST attribute_designator_AST = null;
		
		try {      // for error handling
			simple_name();
			astFactory.addASTChild(currentAST, returnAST);
			attribute_designator_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_44);
			} else {
			  throw ex;
			}
		}
		returnAST = attribute_designator_AST;
	}
	
	public final void tic_attribute_designator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST tic_attribute_designator_AST = null;
		
		try {      // for error handling
			AST tmp62_AST = null;
			tmp62_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp62_AST);
			match(TIC_SIMPLE_NAME);
			tic_attribute_designator_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		returnAST = tic_attribute_designator_AST;
	}
	
	public final void attribute_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST attribute_specification_AST = null;
		
		try {      // for error handling
			AST tmp63_AST = null;
			tmp63_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp63_AST);
			match(K_ATTRIBUTE);
			attribute_designator();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp64_AST = null;
			tmp64_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp64_AST);
			match(K_OF);
			entity_specification();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp65_AST = null;
			tmp65_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp65_AST);
			match(K_IS);
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp66_AST = null;
			tmp66_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp66_AST);
			match(SEMI);
			attribute_specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_45);
			} else {
			  throw ex;
			}
		}
		returnAST = attribute_specification_AST;
	}
	
	public final void entity_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_specification_AST = null;
		
		try {      // for error handling
			entity_name_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp67_AST = null;
			tmp67_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp67_AST);
			match(COLON);
			entity_class();
			astFactory.addASTChild(currentAST, returnAST);
			entity_specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_46);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_specification_AST;
	}
	
	public final void base_unit_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST base_unit_declaration_AST = null;
		
		try {      // for error handling
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			base_unit_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_47);
			} else {
			  throw ex;
			}
		}
		returnAST = base_unit_declaration_AST;
	}
	
	public final void binding_indication() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST binding_indication_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_USE:
			{
				AST tmp68_AST = null;
				tmp68_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp68_AST);
				match(K_USE);
				entity_aspect();
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			binding_indication_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = binding_indication_AST;
	}
	
	public final void entity_aspect() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_aspect_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ENTITY:
			{
				AST tmp69_AST = null;
				tmp69_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp69_AST);
				match(K_ENTITY);
				name();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					AST tmp70_AST = null;
					tmp70_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp70_AST);
					match(LPAREN);
					identifier();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp71_AST = null;
					tmp71_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp71_AST);
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
				entity_aspect_AST = (AST)currentAST.root;
				break;
			}
			case K_CONFIGURATION:
			{
				AST tmp72_AST = null;
				tmp72_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp72_AST);
				match(K_CONFIGURATION);
				name();
				astFactory.addASTChild(currentAST, returnAST);
				entity_aspect_AST = (AST)currentAST.root;
				break;
			}
			case K_OPEN:
			{
				AST tmp73_AST = null;
				tmp73_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp73_AST);
				match(K_OPEN);
				entity_aspect_AST = (AST)currentAST.root;
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
		returnAST = entity_aspect_AST;
	}
	
	public final void generic_map_aspect() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_map_aspect_AST = null;
		
		try {      // for error handling
			AST tmp74_AST = null;
			tmp74_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp74_AST);
			match(K_GENERIC);
			AST tmp75_AST = null;
			tmp75_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp75_AST);
			match(K_MAP);
			AST tmp76_AST = null;
			tmp76_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp76_AST);
			match(LPAREN);
			association_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp77_AST = null;
			tmp77_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp77_AST);
			match(RPAREN);
			generic_map_aspect_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_49);
			} else {
			  throw ex;
			}
		}
		returnAST = generic_map_aspect_AST;
	}
	
	public final void port_map_aspect() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST port_map_aspect_AST = null;
		
		try {      // for error handling
			AST tmp78_AST = null;
			tmp78_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp78_AST);
			match(K_PORT);
			AST tmp79_AST = null;
			tmp79_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp79_AST);
			match(K_MAP);
			AST tmp80_AST = null;
			tmp80_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp80_AST);
			match(LPAREN);
			association_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp81_AST = null;
			tmp81_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp81_AST);
			match(RPAREN);
			port_map_aspect_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = port_map_aspect_AST;
	}
	
	public final void bit_string_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST bit_string_literal_AST = null;
		
		try {      // for error handling
			AST tmp82_AST = null;
			tmp82_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp82_AST);
			match(BIT_STRING_LITERAL);
			bit_string_literal_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = bit_string_literal_AST;
	}
	
	public final void block_configuration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST block_configuration_AST = null;
		
		try {      // for error handling
			AST tmp83_AST = null;
			tmp83_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp83_AST);
			match(K_FOR);
			block_specification();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop57:
			do {
				if ((LA(1)==K_USE)) {
					use_clause();
					astFactory.addASTChild(currentAST, returnAST);
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
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop59;
				}
				
			} while (true);
			}
			AST tmp84_AST = null;
			tmp84_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp84_AST);
			match(K_END);
			AST tmp85_AST = null;
			tmp85_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp85_AST);
			match(K_FOR);
			AST tmp86_AST = null;
			tmp86_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp86_AST);
			match(SEMI);
			block_configuration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_50);
			} else {
			  throw ex;
			}
		}
		returnAST = block_configuration_AST;
	}
	
	public final void block_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST block_specification_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp87_AST = null;
				tmp87_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp87_AST);
				match(LPAREN);
				index_specification();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp88_AST = null;
				tmp88_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp88_AST);
				match(RPAREN);
				block_specification_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_51.member(LA(2)))) {
				name();
				astFactory.addASTChild(currentAST, returnAST);
				block_specification_AST = (AST)currentAST.root;
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
		returnAST = block_specification_AST;
	}
	
	public final void use_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST use_clause_AST = null;
		
		try {      // for error handling
			AST tmp89_AST = null;
			tmp89_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp89_AST);
			match(K_USE);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop597:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp90_AST = null;
					tmp90_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp90_AST);
					match(COMMA);
					name();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop597;
				}
				
			} while (true);
			}
			AST tmp91_AST = null;
			tmp91_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp91_AST);
			match(SEMI);
			use_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_53);
			} else {
			  throw ex;
			}
		}
		returnAST = use_clause_AST;
	}
	
	public final void configuration_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST configuration_item_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				configuration_item_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==K_FOR) && (_tokenSet_54.member(LA(2)))) {
				component_configuration();
				astFactory.addASTChild(currentAST, returnAST);
				configuration_item_AST = (AST)currentAST.root;
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
		returnAST = configuration_item_AST;
	}
	
	public final void subprogram_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subprogram_declaration_AST = null;
		
		try {      // for error handling
			subprogram_specification();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp92_AST = null;
			tmp92_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp92_AST);
			match(SEMI);
			subprogram_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = subprogram_declaration_AST;
	}
	
	public final void subprogram_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subprogram_body_AST = null;
		
		try {      // for error handling
			subprogram_specification();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp93_AST = null;
			tmp93_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp93_AST);
			match(K_IS);
			subprogram_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp94_AST = null;
			tmp94_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp94_AST);
			match(K_BEGIN);
			subprogram_statement_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp95_AST = null;
			tmp95_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp95_AST);
			match(K_END);
			{
			switch ( LA(1)) {
			case K_PROCEDURE:
			case K_FUNCTION:
			{
				subprogram_kind();
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp96_AST = null;
			tmp96_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp96_AST);
			match(SEMI);
			subprogram_body_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_45);
			} else {
			  throw ex;
			}
		}
		returnAST = subprogram_body_AST;
	}
	
	public final void type_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST type_declaration_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				type_declaration_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==K_TYPE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
				incomplete_type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				type_declaration_AST = (AST)currentAST.root;
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
		returnAST = type_declaration_AST;
	}
	
	public final void subtype_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subtype_declaration_AST = null;
		
		try {      // for error handling
			AST tmp97_AST = null;
			tmp97_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp97_AST);
			match(K_SUBTYPE);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp98_AST = null;
			tmp98_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp98_AST);
			match(K_IS);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp99_AST = null;
			tmp99_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp99_AST);
			match(SEMI);
			subtype_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = subtype_declaration_AST;
	}
	
	public final void constant_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST constant_declaration_AST = null;
		
		try {      // for error handling
			AST tmp100_AST = null;
			tmp100_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp100_AST);
			match(K_CONSTANT);
			identifier_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp101_AST = null;
			tmp101_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp101_AST);
			match(COLON);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				AST tmp102_AST = null;
				tmp102_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp102_AST);
				match(COLONEQ);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp103_AST = null;
			tmp103_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp103_AST);
			match(SEMI);
			constant_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = constant_declaration_AST;
	}
	
	public final void signal_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signal_declaration_AST = null;
		
		try {      // for error handling
			AST tmp104_AST = null;
			tmp104_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp104_AST);
			match(K_SIGNAL);
			identifier_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp105_AST = null;
			tmp105_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp105_AST);
			match(COLON);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_BUS:
			case K_REGISTER:
			{
				signal_kind();
				astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp106_AST = null;
				tmp106_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp106_AST);
				match(COLONEQ);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp107_AST = null;
			tmp107_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp107_AST);
			match(SEMI);
			signal_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = signal_declaration_AST;
	}
	
	public final void variable_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_declaration_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_SHARED:
			{
				AST tmp108_AST = null;
				tmp108_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp108_AST);
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
			AST tmp109_AST = null;
			tmp109_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp109_AST);
			match(K_VARIABLE);
			identifier_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp110_AST = null;
			tmp110_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp110_AST);
			match(COLON);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				AST tmp111_AST = null;
				tmp111_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp111_AST);
				match(COLONEQ);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp112_AST = null;
			tmp112_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp112_AST);
			match(SEMI);
			variable_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = variable_declaration_AST;
	}
	
	public final void file_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST file_declaration_AST = null;
		
		try {      // for error handling
			AST tmp113_AST = null;
			tmp113_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp113_AST);
			match(K_FILE);
			identifier_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp114_AST = null;
			tmp114_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp114_AST);
			match(COLON);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_OPEN:
			case K_IS:
			{
				file_open_information();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp115_AST = null;
			tmp115_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp115_AST);
			match(SEMI);
			file_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = file_declaration_AST;
	}
	
	public final void component_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST component_declaration_AST = null;
		
		try {      // for error handling
			AST tmp116_AST = null;
			tmp116_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp116_AST);
			match(K_COMPONENT);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_IS:
			{
				AST tmp117_AST = null;
				tmp117_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp117_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp118_AST = null;
			tmp118_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp118_AST);
			match(K_END);
			AST tmp119_AST = null;
			tmp119_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp119_AST);
			match(K_COMPONENT);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp120_AST = null;
			tmp120_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp120_AST);
			match(SEMI);
			component_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = component_declaration_AST;
	}
	
	public final void configuration_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST configuration_specification_AST = null;
		
		try {      // for error handling
			AST tmp121_AST = null;
			tmp121_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp121_AST);
			match(K_FOR);
			component_specification();
			astFactory.addASTChild(currentAST, returnAST);
			binding_indication();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp122_AST = null;
			tmp122_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp122_AST);
			match(SEMI);
			configuration_specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_29);
			} else {
			  throw ex;
			}
		}
		returnAST = configuration_specification_AST;
	}
	
	public final void disconnection_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST disconnection_specification_AST = null;
		
		try {      // for error handling
			AST tmp123_AST = null;
			tmp123_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp123_AST);
			match(K_DISCONNECT);
			guarded_signal_specification();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp124_AST = null;
			tmp124_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp124_AST);
			match(K_AFTER);
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp125_AST = null;
			tmp125_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp125_AST);
			match(SEMI);
			disconnection_specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_45);
			} else {
			  throw ex;
			}
		}
		returnAST = disconnection_specification_AST;
	}
	
	public final void group_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST group_declaration_AST = null;
		
		try {      // for error handling
			AST tmp126_AST = null;
			tmp126_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp126_AST);
			match(K_GROUP);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp127_AST = null;
			tmp127_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp127_AST);
			match(COLON);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp128_AST = null;
			tmp128_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp128_AST);
			match(LPAREN);
			group_constituent_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp129_AST = null;
			tmp129_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp129_AST);
			match(RPAREN);
			AST tmp130_AST = null;
			tmp130_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp130_AST);
			match(SEMI);
			group_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = group_declaration_AST;
	}
	
	public final void group_template_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST group_template_declaration_AST = null;
		
		try {      // for error handling
			AST tmp131_AST = null;
			tmp131_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp131_AST);
			match(K_GROUP);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp132_AST = null;
			tmp132_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp132_AST);
			match(K_IS);
			AST tmp133_AST = null;
			tmp133_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp133_AST);
			match(LPAREN);
			entity_class_entry_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp134_AST = null;
			tmp134_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp134_AST);
			match(RPAREN);
			AST tmp135_AST = null;
			tmp135_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp135_AST);
			match(SEMI);
			group_template_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = group_template_declaration_AST;
	}
	
	public final void block_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST block_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop69:
			do {
				if ((_tokenSet_22.member(LA(1)))) {
					block_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop69;
				}
				
			} while (true);
			}
			block_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
		returnAST = block_declarative_part_AST;
	}
	
	public final void block_header() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST block_header_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_clause();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case K_GENERIC:
				{
					generic_map_aspect();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp136_AST = null;
					tmp136_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp136_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case K_PORT:
				{
					port_map_aspect();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp137_AST = null;
					tmp137_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp137_AST);
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
			block_header_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_29);
			} else {
			  throw ex;
			}
		}
		returnAST = block_header_AST;
	}
	
	public final void generic_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_clause_AST = null;
		
		try {      // for error handling
			AST tmp138_AST = null;
			tmp138_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp138_AST);
			match(K_GENERIC);
			AST tmp139_AST = null;
			tmp139_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp139_AST);
			match(LPAREN);
			generic_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp140_AST = null;
			tmp140_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp140_AST);
			match(RPAREN);
			AST tmp141_AST = null;
			tmp141_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp141_AST);
			match(SEMI);
			generic_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_55);
			} else {
			  throw ex;
			}
		}
		returnAST = generic_clause_AST;
	}
	
	public final void port_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST port_clause_AST = null;
		
		try {      // for error handling
			AST tmp142_AST = null;
			tmp142_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp142_AST);
			match(K_PORT);
			AST tmp143_AST = null;
			tmp143_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp143_AST);
			match(LPAREN);
			port_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp144_AST = null;
			tmp144_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp144_AST);
			match(RPAREN);
			AST tmp145_AST = null;
			tmp145_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp145_AST);
			match(SEMI);
			port_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_56);
			} else {
			  throw ex;
			}
		}
		returnAST = port_clause_AST;
	}
	
	public final Token  label() throws RecognitionException, TokenStreamException {
		Token tok;
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST label_AST = null;
		tok=null;
		
		try {      // for error handling
			tok=identifier();
			astFactory.addASTChild(currentAST, returnAST);
			label_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_57);
			} else {
			  throw ex;
			}
		}
		returnAST = label_AST;
		return tok;
	}
	
	public final void index_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST index_specification_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				index_specification_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_59.member(LA(2)))) {
				expression();
				astFactory.addASTChild(currentAST, returnAST);
				index_specification_AST = (AST)currentAST.root;
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
		returnAST = index_specification_AST;
	}
	
	public final void block_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST block_statement_AST = null;
		
		try {      // for error handling
			label();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp146_AST = null;
			tmp146_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp146_AST);
			match(COLON);
			AST tmp147_AST = null;
			tmp147_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp147_AST);
			match(K_BLOCK);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				AST tmp148_AST = null;
				tmp148_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp148_AST);
				match(LPAREN);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp149_AST = null;
				tmp149_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp149_AST);
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
				AST tmp150_AST = null;
				tmp150_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp150_AST);
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
			astFactory.addASTChild(currentAST, returnAST);
			block_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp151_AST = null;
			tmp151_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp151_AST);
			match(K_BEGIN);
			block_statement_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp152_AST = null;
			tmp152_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp152_AST);
			match(K_END);
			AST tmp153_AST = null;
			tmp153_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp153_AST);
			match(K_BLOCK);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp154_AST = null;
			tmp154_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp154_AST);
			match(SEMI);
			block_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		returnAST = block_statement_AST;
	}
	
	public final void block_statement_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST block_statement_part_AST = null;
		
		try {      // for error handling
			{
			_loop84:
			do {
				if ((_tokenSet_24.member(LA(1)))) {
					concurrent_statement();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop84;
				}
				
			} while (true);
			}
			block_statement_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = block_statement_part_AST;
	}
	
	public final void case_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST case_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp155_AST = null;
			tmp155_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp155_AST);
			match(K_CASE);
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp156_AST = null;
			tmp156_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp156_AST);
			match(K_IS);
			{
			int _cnt88=0;
			_loop88:
			do {
				if ((LA(1)==K_WHEN)) {
					case_statement_alternative();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt88>=1 ) { break _loop88; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt88++;
			} while (true);
			}
			AST tmp157_AST = null;
			tmp157_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp157_AST);
			match(K_END);
			AST tmp158_AST = null;
			tmp158_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp158_AST);
			match(K_CASE);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp159_AST = null;
			tmp159_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp159_AST);
			match(SEMI);
			case_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = case_statement_AST;
	}
	
	public final void case_statement_alternative() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST case_statement_alternative_AST = null;
		
		try {      // for error handling
			AST tmp160_AST = null;
			tmp160_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp160_AST);
			match(K_WHEN);
			choices();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp161_AST = null;
			tmp161_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp161_AST);
			match(EQGRT);
			sequence_of_statements();
			astFactory.addASTChild(currentAST, returnAST);
			case_statement_alternative_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_60);
			} else {
			  throw ex;
			}
		}
		returnAST = case_statement_alternative_AST;
	}
	
	public final void choices() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST choices_AST = null;
		
		try {      // for error handling
			choice();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop99:
			do {
				if ((LA(1)==BAR)) {
					AST tmp162_AST = null;
					tmp162_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp162_AST);
					match(BAR);
					choice();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop99;
				}
				
			} while (true);
			}
			choices_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_61);
			} else {
			  throw ex;
			}
		}
		returnAST = choices_AST;
	}
	
	public final void sequence_of_statements() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST sequence_of_statements_AST = null;
		
		try {      // for error handling
			{
			_loop496:
			do {
				if ((_tokenSet_62.member(LA(1)))) {
					sequential_statement();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop496;
				}
				
			} while (true);
			}
			sequence_of_statements_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_63);
			} else {
			  throw ex;
			}
		}
		returnAST = sequence_of_statements_AST;
	}
	
	public final void choice() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST choice_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				choice_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					choice_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_66.member(LA(2)))) {
					discrete_range();
					astFactory.addASTChild(currentAST, returnAST);
					choice_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==K_OTHERS)) {
					AST tmp163_AST = null;
					tmp163_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp163_AST);
					match(K_OTHERS);
					choice_AST = (AST)currentAST.root;
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
			returnAST = choice_AST;
		}
		
	public final void simple_expression() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST simple_expression_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case PLUS:
			case MINUS:
			{
				sign();
				astFactory.addASTChild(currentAST, returnAST);
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
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop553:
			do {
				if (((LA(1) >= PLUS && LA(1) <= AND)) && (_tokenSet_12.member(LA(2)))) {
					adding_operator();
					astFactory.addASTChild(currentAST, returnAST);
					term();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop553;
				}
				
			} while (true);
			}
			simple_expression_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = simple_expression_AST;
	}
	
	public final void discrete_range() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST discrete_range_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				discrete_range_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_68.member(LA(2)))) {
				subtype_indication();
				astFactory.addASTChild(currentAST, returnAST);
				discrete_range_AST = (AST)currentAST.root;
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
		returnAST = discrete_range_AST;
	}
	
	public final void component_configuration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST component_configuration_AST = null;
		
		try {      // for error handling
			AST tmp164_AST = null;
			tmp164_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp164_AST);
			match(K_FOR);
			component_specification();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case SEMI:
			case K_USE:
			case K_GENERIC:
			case K_PORT:
			{
				binding_indication();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp165_AST = null;
				tmp165_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp165_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp166_AST = null;
			tmp166_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp166_AST);
			match(K_END);
			AST tmp167_AST = null;
			tmp167_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp167_AST);
			match(K_FOR);
			AST tmp168_AST = null;
			tmp168_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp168_AST);
			match(SEMI);
			component_configuration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_50);
			} else {
			  throw ex;
			}
		}
		returnAST = component_configuration_AST;
	}
	
	public final void component_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST component_specification_AST = null;
		
		try {      // for error handling
			instantiation_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp169_AST = null;
			tmp169_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp169_AST);
			match(COLON);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			component_specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_70);
			} else {
			  throw ex;
			}
		}
		returnAST = component_specification_AST;
	}
	
	public final void component_instantiation_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST component_instantiation_statement_AST = null;
		Token instNm = null, refNm = null;
		
		try {      // for error handling
			instNm=label();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp170_AST = null;
			tmp170_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp170_AST);
			match(COLON);
			refNm=instantiated_unit();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				stTracker.addInstance(refNm, instNm);
			}
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_map_aspect();
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp171_AST = null;
			tmp171_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp171_AST);
			match(SEMI);
			component_instantiation_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		returnAST = component_instantiation_statement_AST;
	}
	
	public final Token  instantiated_unit() throws RecognitionException, TokenStreamException {
		Token tok;
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instantiated_unit_AST = null;
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
					AST tmp172_AST = null;
					tmp172_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp172_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
				instantiated_unit_AST = (AST)currentAST.root;
				break;
			}
			case K_ENTITY:
			{
				AST tmp173_AST = null;
				tmp173_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp173_AST);
				match(K_ENTITY);
				tok=name();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					AST tmp174_AST = null;
					tmp174_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp174_AST);
					match(LPAREN);
					identifier();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp175_AST = null;
					tmp175_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp175_AST);
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
				instantiated_unit_AST = (AST)currentAST.root;
				break;
			}
			case K_CONFIGURATION:
			{
				AST tmp176_AST = null;
				tmp176_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp176_AST);
				match(K_CONFIGURATION);
				name();
				astFactory.addASTChild(currentAST, returnAST);
				instantiated_unit_AST = (AST)currentAST.root;
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
		returnAST = instantiated_unit_AST;
		return tok;
	}
	
	public final void instantiation_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instantiation_list_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
				{
				_loop303:
				do {
					if ((LA(1)==COMMA)) {
						AST tmp177_AST = null;
						tmp177_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp177_AST);
						match(COMMA);
						label();
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						break _loop303;
					}
					
				} while (true);
				}
				instantiation_list_AST = (AST)currentAST.root;
				break;
			}
			case K_OTHERS:
			{
				AST tmp178_AST = null;
				tmp178_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp178_AST);
				match(K_OTHERS);
				instantiation_list_AST = (AST)currentAST.root;
				break;
			}
			case K_ALL:
			{
				AST tmp179_AST = null;
				tmp179_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp179_AST);
				match(K_ALL);
				instantiation_list_AST = (AST)currentAST.root;
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
		returnAST = instantiation_list_AST;
	}
	
	public final void composite_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST composite_type_definition_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ARRAY:
			{
				array_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				composite_type_definition_AST = (AST)currentAST.root;
				break;
			}
			case K_RECORD:
			{
				record_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				composite_type_definition_AST = (AST)currentAST.root;
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
		returnAST = composite_type_definition_AST;
	}
	
	public final void record_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST record_type_definition_AST = null;
		
		try {      // for error handling
			AST tmp180_AST = null;
			tmp180_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp180_AST);
			match(K_RECORD);
			{
			int _cnt470=0;
			_loop470:
			do {
				if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER)) {
					element_declaration();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt470>=1 ) { break _loop470; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt470++;
			} while (true);
			}
			AST tmp181_AST = null;
			tmp181_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp181_AST);
			match(K_END);
			AST tmp182_AST = null;
			tmp182_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp182_AST);
			match(K_RECORD);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				astFactory.addASTChild(currentAST, returnAST);
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
			record_type_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = record_type_definition_AST;
	}
	
	public final void concurrent_assertion_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST concurrent_assertion_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp183_AST = null;
				tmp183_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp183_AST);
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
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp184_AST = null;
			tmp184_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp184_AST);
			match(SEMI);
			concurrent_assertion_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		returnAST = concurrent_assertion_statement_AST;
	}
	
	public final void concurrent_procedure_call_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST concurrent_procedure_call_statement_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					AST tmp185_AST = null;
					tmp185_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp185_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp186_AST = null;
				tmp186_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp186_AST);
				match(SEMI);
				concurrent_procedure_call_statement_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_32.member(LA(1))) && (_tokenSet_72.member(LA(2)))) {
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					AST tmp187_AST = null;
					tmp187_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp187_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp188_AST = null;
				tmp188_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp188_AST);
				match(SEMI);
				concurrent_procedure_call_statement_AST = (AST)currentAST.root;
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
		returnAST = concurrent_procedure_call_statement_AST;
	}
	
	public final void procedure_call() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST procedure_call_AST = null;
		
		try {      // for error handling
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				AST tmp189_AST = null;
				tmp189_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp189_AST);
				match(LPAREN);
				actual_parameter_part();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp190_AST = null;
				tmp190_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp190_AST);
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
			procedure_call_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = procedure_call_AST;
	}
	
	public final void concurrent_signal_assignment_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST concurrent_signal_assignment_statement_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					AST tmp191_AST = null;
					tmp191_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp191_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
				concurrent_signal_assignment_statement_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_36.member(LA(1))) && (_tokenSet_73.member(LA(2)))) {
				{
				switch ( LA(1)) {
				case K_POSTPONED:
				{
					AST tmp192_AST = null;
					tmp192_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp192_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
				concurrent_signal_assignment_statement_AST = (AST)currentAST.root;
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
		returnAST = concurrent_signal_assignment_statement_AST;
	}
	
	public final void concurrent_signal_assignment_statement_2() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST concurrent_signal_assignment_statement_2_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				conditional_signal_assignment();
				astFactory.addASTChild(currentAST, returnAST);
				concurrent_signal_assignment_statement_2_AST = (AST)currentAST.root;
				break;
			}
			case K_WITH:
			{
				selected_signal_assignment();
				astFactory.addASTChild(currentAST, returnAST);
				concurrent_signal_assignment_statement_2_AST = (AST)currentAST.root;
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
		returnAST = concurrent_signal_assignment_statement_2_AST;
	}
	
	public final void conditional_signal_assignment() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conditional_signal_assignment_AST = null;
		
		try {      // for error handling
			target();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp193_AST = null;
			tmp193_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp193_AST);
			match(LSTEQ);
			voptions();
			astFactory.addASTChild(currentAST, returnAST);
			conditional_waveforms();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp194_AST = null;
			tmp194_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp194_AST);
			match(SEMI);
			conditional_signal_assignment_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		returnAST = conditional_signal_assignment_AST;
	}
	
	public final void selected_signal_assignment() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST selected_signal_assignment_AST = null;
		
		try {      // for error handling
			AST tmp195_AST = null;
			tmp195_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp195_AST);
			match(K_WITH);
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp196_AST = null;
			tmp196_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp196_AST);
			match(K_SELECT);
			target();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp197_AST = null;
			tmp197_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp197_AST);
			match(LSTEQ);
			voptions();
			astFactory.addASTChild(currentAST, returnAST);
			selected_waveforms();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp198_AST = null;
			tmp198_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp198_AST);
			match(SEMI);
			selected_signal_assignment_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		returnAST = selected_signal_assignment_AST;
	}
	
	public final void process_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST process_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp199_AST = null;
				tmp199_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp199_AST);
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
			AST tmp200_AST = null;
			tmp200_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp200_AST);
			match(K_PROCESS);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				AST tmp201_AST = null;
				tmp201_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp201_AST);
				match(LPAREN);
				sensitivity_list();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp202_AST = null;
				tmp202_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp202_AST);
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
				AST tmp203_AST = null;
				tmp203_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp203_AST);
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
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp204_AST = null;
			tmp204_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp204_AST);
			match(K_BEGIN);
			process_statement_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp205_AST = null;
			tmp205_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp205_AST);
			match(K_END);
			{
			switch ( LA(1)) {
			case K_POSTPONED:
			{
				AST tmp206_AST = null;
				tmp206_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp206_AST);
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
			AST tmp207_AST = null;
			tmp207_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp207_AST);
			match(K_PROCESS);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp208_AST = null;
			tmp208_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp208_AST);
			match(SEMI);
			process_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		returnAST = process_statement_AST;
	}
	
	public final void generate_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generate_statement_AST = null;
		
		try {      // for error handling
			label();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp209_AST = null;
			tmp209_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp209_AST);
			match(COLON);
			generation_scheme();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp210_AST = null;
			tmp210_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp210_AST);
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
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						break _loop265;
					}
					
				} while (true);
				}
				AST tmp211_AST = null;
				tmp211_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp211_AST);
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
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop267;
				}
				
			} while (true);
			}
			AST tmp212_AST = null;
			tmp212_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp212_AST);
			match(K_END);
			AST tmp213_AST = null;
			tmp213_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp213_AST);
			match(K_GENERATE);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp214_AST = null;
			tmp214_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp214_AST);
			match(SEMI);
			generate_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		returnAST = generate_statement_AST;
	}
	
	public final void condition_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST condition_clause_AST = null;
		
		try {      // for error handling
			AST tmp215_AST = null;
			tmp215_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp215_AST);
			match(K_UNTIL);
			condition();
			astFactory.addASTChild(currentAST, returnAST);
			condition_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_74);
			} else {
			  throw ex;
			}
		}
		returnAST = condition_clause_AST;
	}
	
	public final void target() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST target_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				astFactory.addASTChild(currentAST, returnAST);
				target_AST = (AST)currentAST.root;
				break;
			}
			case LPAREN:
			{
				aggregate();
				astFactory.addASTChild(currentAST, returnAST);
				target_AST = (AST)currentAST.root;
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
		returnAST = target_AST;
	}
	
	public final void voptions() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST voptions_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_GUARDED:
			{
				AST tmp216_AST = null;
				tmp216_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp216_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			voptions_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_76);
			} else {
			  throw ex;
			}
		}
		returnAST = voptions_AST;
	}
	
	public final void conditional_waveforms() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conditional_waveforms_AST = null;
		
		try {      // for error handling
			waveform();
			astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp217_AST = null;
				tmp217_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp217_AST);
				match(K_WHEN);
				condition();
				astFactory.addASTChild(currentAST, returnAST);
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
			conditional_waveforms_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = conditional_waveforms_AST;
	}
	
	public final void waveform() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST waveform_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				{
				_loop610:
				do {
					if ((LA(1)==COMMA)) {
						AST tmp218_AST = null;
						tmp218_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp218_AST);
						match(COMMA);
						waveform_element();
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						break _loop610;
					}
					
				} while (true);
				}
				waveform_AST = (AST)currentAST.root;
				break;
			}
			case K_UNAFFECTED:
			{
				AST tmp219_AST = null;
				tmp219_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp219_AST);
				match(K_UNAFFECTED);
				waveform_AST = (AST)currentAST.root;
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
		returnAST = waveform_AST;
	}
	
	public final void conditional_waveforms_2() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST conditional_waveforms_2_AST = null;
		
		try {      // for error handling
			AST tmp220_AST = null;
			tmp220_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp220_AST);
			match(K_WHEN);
			condition();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp221_AST = null;
			tmp221_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp221_AST);
			match(K_ELSE);
			waveform();
			astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((LA(1)==SEMI||LA(1)==K_WHEN) && (_tokenSet_77.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			conditional_waveforms_2_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_78);
			} else {
			  throw ex;
			}
		}
		returnAST = conditional_waveforms_2_AST;
	}
	
	public final void configuration_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST configuration_declaration_AST = null;
		
		try {      // for error handling
			AST tmp222_AST = null;
			tmp222_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp222_AST);
			match(K_CONFIGURATION);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp223_AST = null;
			tmp223_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp223_AST);
			match(K_OF);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp224_AST = null;
			tmp224_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp224_AST);
			match(K_IS);
			configuration_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			block_configuration();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp225_AST = null;
			tmp225_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp225_AST);
			match(K_END);
			{
			switch ( LA(1)) {
			case K_CONFIGURATION:
			{
				AST tmp226_AST = null;
				tmp226_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp226_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp227_AST = null;
			tmp227_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp227_AST);
			match(SEMI);
			configuration_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		returnAST = configuration_declaration_AST;
	}
	
	public final void configuration_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST configuration_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop158:
			do {
				if ((LA(1)==K_ATTRIBUTE||LA(1)==K_USE||LA(1)==K_GROUP)) {
					configuration_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop158;
				}
				
			} while (true);
			}
			configuration_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_79);
			} else {
			  throw ex;
			}
		}
		returnAST = configuration_declarative_part_AST;
	}
	
	public final void configuration_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST configuration_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				configuration_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ATTRIBUTE:
			{
				attribute_specification();
				astFactory.addASTChild(currentAST, returnAST);
				configuration_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_GROUP:
			{
				group_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				configuration_declarative_item_AST = (AST)currentAST.root;
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
		returnAST = configuration_declarative_item_AST;
	}
	
	public final void identifier_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST identifier_list_AST = null;
		
		try {      // for error handling
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop283:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp228_AST = null;
					tmp228_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp228_AST);
					match(COMMA);
					identifier();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop283;
				}
				
			} while (true);
			}
			identifier_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_71);
			} else {
			  throw ex;
			}
		}
		returnAST = identifier_list_AST;
	}
	
	public final void index_constraint() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST index_constraint_AST = null;
		
		try {      // for error handling
			AST tmp229_AST = null;
			tmp229_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp229_AST);
			match(LPAREN);
			discrete_range();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop293:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp230_AST = null;
					tmp230_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp230_AST);
					match(COMMA);
					discrete_range();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop293;
				}
				
			} while (true);
			}
			AST tmp231_AST = null;
			tmp231_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp231_AST);
			match(RPAREN);
			index_constraint_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_81);
			} else {
			  throw ex;
			}
		}
		returnAST = index_constraint_AST;
	}
	
	public final void constraint() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST constraint_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_RANGE:
			{
				range_constraint();
				astFactory.addASTChild(currentAST, returnAST);
				constraint_AST = (AST)currentAST.root;
				break;
			}
			case LPAREN:
			{
				index_constraint();
				astFactory.addASTChild(currentAST, returnAST);
				constraint_AST = (AST)currentAST.root;
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
		returnAST = constraint_AST;
	}
	
	public final void range_constraint() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST range_constraint_AST = null;
		
		try {      // for error handling
			AST tmp232_AST = null;
			tmp232_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp232_AST);
			match(K_RANGE);
			range();
			astFactory.addASTChild(currentAST, returnAST);
			range_constraint_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = range_constraint_AST;
	}
	
	public final void context_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST context_clause_AST = null;
		
		try {      // for error handling
			{
			_loop169:
			do {
				if ((LA(1)==K_USE||LA(1)==K_LIBRARY)) {
					context_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop169;
				}
				
			} while (true);
			}
			context_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_82);
			} else {
			  throw ex;
			}
		}
		returnAST = context_clause_AST;
	}
	
	public final void context_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST context_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_LIBRARY:
			{
				library_clause();
				astFactory.addASTChild(currentAST, returnAST);
				context_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				context_item_AST = (AST)currentAST.root;
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
		returnAST = context_item_AST;
	}
	
	public final void library_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST library_clause_AST = null;
		
		try {      // for error handling
			AST tmp233_AST = null;
			tmp233_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp233_AST);
			match(K_LIBRARY);
			logical_name_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp234_AST = null;
			tmp234_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp234_AST);
			match(SEMI);
			library_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_83);
			} else {
			  throw ex;
			}
		}
		returnAST = library_clause_AST;
	}
	
	public final void declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST declaration_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_ATTRIBUTE:
			{
				attribute_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_COMPONENT:
			{
				component_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_ENTITY:
			{
				entity_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_CONFIGURATION:
			{
				configuration_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_PROCEDURE:
			case K_FUNCTION:
			case K_PURE:
			case K_IMPURE:
			{
				subprogram_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_PACKAGE:
			{
				package_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				declaration_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					declaration_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_85.member(LA(1))) && (_tokenSet_86.member(LA(2)))) {
					interface_declaration();
					astFactory.addASTChild(currentAST, returnAST);
					declaration_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						declaration_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						group_template_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						declaration_AST = (AST)currentAST.root;
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
			returnAST = declaration_AST;
		}
		
	public final void object_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST object_declaration_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				object_declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				object_declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				object_declaration_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				object_declaration_AST = (AST)currentAST.root;
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
		returnAST = object_declaration_AST;
	}
	
	public final void interface_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_declaration_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				interface_declaration_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					interface_declaration_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==K_VARIABLE||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_86.member(LA(2)))) {
					interface_variable_declaration();
					astFactory.addASTChild(currentAST, returnAST);
					interface_declaration_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==K_FILE)) {
					interface_file_declaration();
					astFactory.addASTChild(currentAST, returnAST);
					interface_declaration_AST = (AST)currentAST.root;
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
			returnAST = interface_declaration_AST;
		}
		
	public final void entity_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_declaration_AST = null;
		Token id = null;
		
		try {      // for error handling
			AST tmp235_AST = null;
			tmp235_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp235_AST);
			match(K_ENTITY);
			id=identifier();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				stTracker.beginEntityDecl(id);
			}
			AST tmp236_AST = null;
			tmp236_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp236_AST);
			match(K_IS);
			entity_header();
			astFactory.addASTChild(currentAST, returnAST);
			entity_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_BEGIN:
			{
				AST tmp237_AST = null;
				tmp237_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp237_AST);
				match(K_BEGIN);
				entity_statement_part();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp238_AST = null;
			tmp238_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp238_AST);
			match(K_END);
			{
			switch ( LA(1)) {
			case K_ENTITY:
			{
				AST tmp239_AST = null;
				tmp239_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp239_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp240_AST = null;
			tmp240_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp240_AST);
			match(SEMI);
			if ( inputState.guessing==0 ) {
				stTracker.endEntityDecl();
			}
			entity_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_declaration_AST;
	}
	
	public final void package_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST package_declaration_AST = null;
		
		try {      // for error handling
			AST tmp241_AST = null;
			tmp241_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp241_AST);
			match(K_PACKAGE);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp242_AST = null;
			tmp242_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp242_AST);
			match(K_IS);
			package_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp243_AST = null;
			tmp243_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp243_AST);
			match(K_END);
			{
			switch ( LA(1)) {
			case K_PACKAGE:
			{
				AST tmp244_AST = null;
				tmp244_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp244_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp245_AST = null;
			tmp245_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp245_AST);
			match(SEMI);
			package_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		returnAST = package_declaration_AST;
	}
	
	public final void delay_mechanism() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST delay_mechanism_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TRANSPORT:
			{
				AST tmp246_AST = null;
				tmp246_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp246_AST);
				match(K_TRANSPORT);
				delay_mechanism_AST = (AST)currentAST.root;
				break;
			}
			case K_REJECT:
			case K_INERTIAL:
			{
				{
				switch ( LA(1)) {
				case K_REJECT:
				{
					AST tmp247_AST = null;
					tmp247_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp247_AST);
					match(K_REJECT);
					expression();
					astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp248_AST = null;
				tmp248_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp248_AST);
				match(K_INERTIAL);
				delay_mechanism_AST = (AST)currentAST.root;
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
		returnAST = delay_mechanism_AST;
	}
	
	public final void design_file() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST design_file_AST = null;
		
		try {      // for error handling
			{
			int _cnt181=0;
			_loop181:
			do {
				if ((_tokenSet_83.member(LA(1)))) {
					design_unit();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt181>=1 ) { break _loop181; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt181++;
			} while (true);
			}
			design_file_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_87);
			} else {
			  throw ex;
			}
		}
		returnAST = design_file_AST;
	}
	
	public final void design_unit() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST design_unit_AST = null;
		
		try {      // for error handling
			context_clause();
			astFactory.addASTChild(currentAST, returnAST);
			library_unit();
			astFactory.addASTChild(currentAST, returnAST);
			design_unit_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		returnAST = design_unit_AST;
	}
	
	public final void library_unit() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST library_unit_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				library_unit_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==K_CONFIGURATION||LA(1)==K_ENTITY||LA(1)==K_PACKAGE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
				primary_unit();
				astFactory.addASTChild(currentAST, returnAST);
				library_unit_AST = (AST)currentAST.root;
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
		returnAST = library_unit_AST;
	}
	
	public final void designator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST designator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				identifier();
				astFactory.addASTChild(currentAST, returnAST);
				designator_AST = (AST)currentAST.root;
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				astFactory.addASTChild(currentAST, returnAST);
				designator_AST = (AST)currentAST.root;
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
		returnAST = designator_AST;
	}
	
	public final void direction() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST direction_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TO:
			{
				AST tmp249_AST = null;
				tmp249_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp249_AST);
				match(K_TO);
				direction_AST = (AST)currentAST.root;
				break;
			}
			case K_DOWNTO:
			{
				AST tmp250_AST = null;
				tmp250_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp250_AST);
				match(K_DOWNTO);
				direction_AST = (AST)currentAST.root;
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
		returnAST = direction_AST;
	}
	
	public final void guarded_signal_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST guarded_signal_specification_AST = null;
		
		try {      // for error handling
			signal_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp251_AST = null;
			tmp251_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp251_AST);
			match(COLON);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			guarded_signal_specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_90);
			} else {
			  throw ex;
			}
		}
		returnAST = guarded_signal_specification_AST;
	}
	
	public final void range() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST range_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				direction();
				astFactory.addASTChild(currentAST, returnAST);
				simple_expression();
				astFactory.addASTChild(currentAST, returnAST);
				range_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_92.member(LA(2)))) {
				name();
				astFactory.addASTChild(currentAST, returnAST);
				range_AST = (AST)currentAST.root;
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
		returnAST = range_AST;
	}
	
	public final void element_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST element_declaration_AST = null;
		
		try {      // for error handling
			identifier_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp252_AST = null;
			tmp252_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp252_AST);
			match(COLON);
			element_subtype_definition();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp253_AST = null;
			tmp253_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp253_AST);
			match(SEMI);
			element_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_47);
			} else {
			  throw ex;
			}
		}
		returnAST = element_declaration_AST;
	}
	
	public final void element_subtype_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST element_subtype_definition_AST = null;
		
		try {      // for error handling
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			element_subtype_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = element_subtype_definition_AST;
	}
	
	public final void entity_class() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_class_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ENTITY:
			{
				AST tmp254_AST = null;
				tmp254_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp254_AST);
				match(K_ENTITY);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_PROCEDURE:
			{
				AST tmp255_AST = null;
				tmp255_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp255_AST);
				match(K_PROCEDURE);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_TYPE:
			{
				AST tmp256_AST = null;
				tmp256_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp256_AST);
				match(K_TYPE);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_SIGNAL:
			{
				AST tmp257_AST = null;
				tmp257_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp257_AST);
				match(K_SIGNAL);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_LABEL:
			{
				AST tmp258_AST = null;
				tmp258_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp258_AST);
				match(K_LABEL);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_ARCHITECTURE:
			{
				AST tmp259_AST = null;
				tmp259_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp259_AST);
				match(K_ARCHITECTURE);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_FUNCTION:
			{
				AST tmp260_AST = null;
				tmp260_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp260_AST);
				match(K_FUNCTION);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				AST tmp261_AST = null;
				tmp261_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp261_AST);
				match(K_SUBTYPE);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			{
				AST tmp262_AST = null;
				tmp262_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp262_AST);
				match(K_VARIABLE);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_LITERAL:
			{
				AST tmp263_AST = null;
				tmp263_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp263_AST);
				match(K_LITERAL);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_CONFIGURATION:
			{
				AST tmp264_AST = null;
				tmp264_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp264_AST);
				match(K_CONFIGURATION);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_PACKAGE:
			{
				AST tmp265_AST = null;
				tmp265_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp265_AST);
				match(K_PACKAGE);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				AST tmp266_AST = null;
				tmp266_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp266_AST);
				match(K_CONSTANT);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_COMPONENT:
			{
				AST tmp267_AST = null;
				tmp267_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp267_AST);
				match(K_COMPONENT);
				entity_class_AST = (AST)currentAST.root;
				break;
			}
			case K_UNITS:
			{
				AST tmp268_AST = null;
				tmp268_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp268_AST);
				match(K_UNITS);
				entity_class_AST = (AST)currentAST.root;
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
		returnAST = entity_class_AST;
	}
	
	public final void entity_class_entry() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_class_entry_AST = null;
		
		try {      // for error handling
			entity_class();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LSTGRT:
			{
				AST tmp269_AST = null;
				tmp269_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp269_AST);
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
			entity_class_entry_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_class_entry_AST;
	}
	
	public final void entity_class_entry_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_class_entry_list_AST = null;
		
		try {      // for error handling
			entity_class_entry();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop202:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp270_AST = null;
					tmp270_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp270_AST);
					match(COMMA);
					entity_class_entry();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop202;
				}
				
			} while (true);
			}
			entity_class_entry_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_class_entry_list_AST;
	}
	
	public final void entity_header() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_header_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_GENERIC:
			{
				generic_clause();
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			entity_header_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_94);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_header_AST;
	}
	
	public final void entity_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop216:
			do {
				if ((_tokenSet_95.member(LA(1)))) {
					entity_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop216;
				}
				
			} while (true);
			}
			entity_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_96);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_declarative_part_AST;
	}
	
	public final void entity_statement_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_statement_part_AST = null;
		
		try {      // for error handling
			{
			_loop233:
			do {
				if ((_tokenSet_97.member(LA(1)))) {
					entity_statement();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop233;
				}
				
			} while (true);
			}
			entity_statement_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_statement_part_AST;
	}
	
	public final void entity_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_DISCONNECT:
			{
				disconnection_specification();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				entity_declarative_item_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					entity_declarative_item_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
					astFactory.addASTChild(currentAST, returnAST);
					entity_declarative_item_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						entity_declarative_item_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						entity_declarative_item_AST = (AST)currentAST.root;
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
							astFactory.addASTChild(currentAST, returnAST);
							entity_declarative_item_AST = (AST)currentAST.root;
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
							astFactory.addASTChild(currentAST, returnAST);
							entity_declarative_item_AST = (AST)currentAST.root;
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
				returnAST = entity_declarative_item_AST;
			}
			
	public final void entity_designator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_designator_AST = null;
		
		try {      // for error handling
			entity_tag();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LBRACK:
			{
				signature();
				astFactory.addASTChild(currentAST, returnAST);
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
			entity_designator_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_98);
			} else {
			  throw ex;
			}
		}
		returnAST = entity_designator_AST;
	}
	
	public final void entity_tag() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_tag_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				astFactory.addASTChild(currentAST, returnAST);
				entity_tag_AST = (AST)currentAST.root;
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				astFactory.addASTChild(currentAST, returnAST);
				entity_tag_AST = (AST)currentAST.root;
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				astFactory.addASTChild(currentAST, returnAST);
				entity_tag_AST = (AST)currentAST.root;
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
		returnAST = entity_tag_AST;
	}
	
	public final void entity_name_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_name_list_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case CHARACTER_LITERAL:
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				entity_designator();
				astFactory.addASTChild(currentAST, returnAST);
				{
				_loop224:
				do {
					if ((LA(1)==COMMA)) {
						AST tmp271_AST = null;
						tmp271_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp271_AST);
						match(COMMA);
						entity_designator();
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						break _loop224;
					}
					
				} while (true);
				}
				entity_name_list_AST = (AST)currentAST.root;
				break;
			}
			case K_OTHERS:
			{
				AST tmp272_AST = null;
				tmp272_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp272_AST);
				match(K_OTHERS);
				entity_name_list_AST = (AST)currentAST.root;
				break;
			}
			case K_ALL:
			{
				AST tmp273_AST = null;
				tmp273_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp273_AST);
				match(K_ALL);
				entity_name_list_AST = (AST)currentAST.root;
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
		returnAST = entity_name_list_AST;
	}
	
	public final void entity_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST entity_statement_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				entity_statement_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					entity_statement_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_30.member(LA(1))) && (_tokenSet_31.member(LA(2)))) {
					process_statement();
					astFactory.addASTChild(currentAST, returnAST);
					entity_statement_AST = (AST)currentAST.root;
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
			returnAST = entity_statement_AST;
		}
		
	public final void enumeration_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST enumeration_literal_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				identifier();
				astFactory.addASTChild(currentAST, returnAST);
				enumeration_literal_AST = (AST)currentAST.root;
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				astFactory.addASTChild(currentAST, returnAST);
				enumeration_literal_AST = (AST)currentAST.root;
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
		returnAST = enumeration_literal_AST;
	}
	
	public final void enumeration_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST enumeration_type_definition_AST = null;
		
		try {      // for error handling
			AST tmp274_AST = null;
			tmp274_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp274_AST);
			match(LPAREN);
			enumeration_literal();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop238:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp275_AST = null;
					tmp275_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp275_AST);
					match(COMMA);
					enumeration_literal();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop238;
				}
				
			} while (true);
			}
			AST tmp276_AST = null;
			tmp276_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp276_AST);
			match(RPAREN);
			enumeration_type_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = enumeration_type_definition_AST;
	}
	
	public final void exit_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST exit_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp277_AST = null;
			tmp277_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp277_AST);
			match(K_EXIT);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp278_AST = null;
				tmp278_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp278_AST);
				match(K_WHEN);
				condition();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp279_AST = null;
			tmp279_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp279_AST);
			match(SEMI);
			exit_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = exit_statement_AST;
	}
	
	public final void relation() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST relation_AST = null;
		
		try {      // for error handling
			shift_expression();
			astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
				shift_expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			relation_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_101);
			} else {
			  throw ex;
			}
		}
		returnAST = relation_AST;
	}
	
	public final void logical_op() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST logical_op_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_AND:
			{
				AST tmp280_AST = null;
				tmp280_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp280_AST);
				match(K_AND);
				logical_op_AST = (AST)currentAST.root;
				break;
			}
			case K_OR:
			{
				AST tmp281_AST = null;
				tmp281_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp281_AST);
				match(K_OR);
				logical_op_AST = (AST)currentAST.root;
				break;
			}
			case K_XOR:
			{
				AST tmp282_AST = null;
				tmp282_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp282_AST);
				match(K_XOR);
				logical_op_AST = (AST)currentAST.root;
				break;
			}
			case K_NAND:
			{
				AST tmp283_AST = null;
				tmp283_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp283_AST);
				match(K_NAND);
				logical_op_AST = (AST)currentAST.root;
				break;
			}
			case K_NOR:
			{
				AST tmp284_AST = null;
				tmp284_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp284_AST);
				match(K_NOR);
				logical_op_AST = (AST)currentAST.root;
				break;
			}
			case K_XNOR:
			{
				AST tmp285_AST = null;
				tmp285_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp285_AST);
				match(K_XNOR);
				logical_op_AST = (AST)currentAST.root;
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
		returnAST = logical_op_AST;
	}
	
	public final void factor() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST factor_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				{
				if ((LA(1)==STAR2) && (_tokenSet_102.member(LA(2)))) {
					AST tmp286_AST = null;
					tmp286_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp286_AST);
					match(STAR2);
					primary();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else if ((_tokenSet_2.member(LA(1))) && (_tokenSet_103.member(LA(2)))) {
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				
				}
				factor_AST = (AST)currentAST.root;
				break;
			}
			case K_ABS:
			{
				AST tmp287_AST = null;
				tmp287_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp287_AST);
				match(K_ABS);
				primary();
				astFactory.addASTChild(currentAST, returnAST);
				factor_AST = (AST)currentAST.root;
				break;
			}
			case K_NOT:
			{
				AST tmp288_AST = null;
				tmp288_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp288_AST);
				match(K_NOT);
				primary();
				astFactory.addASTChild(currentAST, returnAST);
				factor_AST = (AST)currentAST.root;
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
		returnAST = factor_AST;
	}
	
	public final void primary() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST primary_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				primary_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					{
					switch ( LA(1)) {
					case LBRACK:
					{
						signature();
						astFactory.addASTChild(currentAST, returnAST);
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
					astFactory.addASTChild(currentAST, returnAST);
					primary_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						primary_AST = (AST)currentAST.root;
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
							AST tmp289_AST = null;
							tmp289_AST = astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp289_AST);
							match(LPAREN);
							expression();
							astFactory.addASTChild(currentAST, returnAST);
							AST tmp290_AST = null;
							tmp290_AST = astFactory.create(LT(1));
							astFactory.addASTChild(currentAST, tmp290_AST);
							match(RPAREN);
							primary_AST = (AST)currentAST.root;
						}
						else if ((_tokenSet_104.member(LA(1))) && (_tokenSet_105.member(LA(2)))) {
							literal();
							astFactory.addASTChild(currentAST, returnAST);
							primary_AST = (AST)currentAST.root;
						}
						else if ((LA(1)==K_NEW)) {
							allocator();
							astFactory.addASTChild(currentAST, returnAST);
							primary_AST = (AST)currentAST.root;
						}
						else if ((LA(1)==LPAREN) && (_tokenSet_14.member(LA(2)))) {
							aggregate();
							astFactory.addASTChild(currentAST, returnAST);
							primary_AST = (AST)currentAST.root;
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
					returnAST = primary_AST;
				}
				
	public final void file_open_information() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST file_open_information_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_OPEN:
			{
				AST tmp291_AST = null;
				tmp291_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp291_AST);
				match(K_OPEN);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp292_AST = null;
			tmp292_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp292_AST);
			match(K_IS);
			file_logical_name();
			astFactory.addASTChild(currentAST, returnAST);
			file_open_information_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = file_open_information_AST;
	}
	
	public final void file_logical_name() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST file_logical_name_AST = null;
		
		try {      // for error handling
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			file_logical_name_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = file_logical_name_AST;
	}
	
	public final void file_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST file_type_definition_AST = null;
		
		try {      // for error handling
			AST tmp293_AST = null;
			tmp293_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp293_AST);
			match(K_FILE);
			AST tmp294_AST = null;
			tmp294_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp294_AST);
			match(K_OF);
			name();
			astFactory.addASTChild(currentAST, returnAST);
			file_type_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = file_type_definition_AST;
	}
	
	public final void floating_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST floating_type_definition_AST = null;
		
		try {      // for error handling
			range_constraint();
			astFactory.addASTChild(currentAST, returnAST);
			floating_type_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_87);
			} else {
			  throw ex;
			}
		}
		returnAST = floating_type_definition_AST;
	}
	
	public final void formal_parameter_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST formal_parameter_list_AST = null;
		
		try {      // for error handling
			interface_list();
			astFactory.addASTChild(currentAST, returnAST);
			formal_parameter_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = formal_parameter_list_AST;
	}
	
	public final void interface_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_list_AST = null;
		
		try {      // for error handling
			interface_element();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop317:
			do {
				if ((LA(1)==SEMI)) {
					AST tmp295_AST = null;
					tmp295_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp295_AST);
					match(SEMI);
					interface_element();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop317;
				}
				
			} while (true);
			}
			interface_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = interface_list_AST;
	}
	
	public final void full_type_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST full_type_declaration_AST = null;
		
		try {      // for error handling
			AST tmp296_AST = null;
			tmp296_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp296_AST);
			match(K_TYPE);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp297_AST = null;
			tmp297_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp297_AST);
			match(K_IS);
			type_definition();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp298_AST = null;
			tmp298_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp298_AST);
			match(SEMI);
			full_type_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = full_type_declaration_AST;
	}
	
	public final void type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST type_definition_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case LPAREN:
			case K_RANGE:
			{
				scalar_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				type_definition_AST = (AST)currentAST.root;
				break;
			}
			case K_ARRAY:
			case K_RECORD:
			{
				composite_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				type_definition_AST = (AST)currentAST.root;
				break;
			}
			case K_ACCESS:
			{
				access_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				type_definition_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				type_definition_AST = (AST)currentAST.root;
				break;
			}
			case K_PROTECTED:
			{
				protected_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				type_definition_AST = (AST)currentAST.root;
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
		returnAST = type_definition_AST;
	}
	
	public final void function_call() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST function_call_AST = null;
		
		try {      // for error handling
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				AST tmp299_AST = null;
				tmp299_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp299_AST);
				match(LPAREN);
				actual_parameter_part();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp300_AST = null;
				tmp300_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp300_AST);
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
			function_call_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = function_call_AST;
	}
	
	public final void generation_scheme() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generation_scheme_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_FOR:
			{
				AST tmp301_AST = null;
				tmp301_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp301_AST);
				match(K_FOR);
				parameter_specification();
				astFactory.addASTChild(currentAST, returnAST);
				generation_scheme_AST = (AST)currentAST.root;
				break;
			}
			case K_IF:
			{
				AST tmp302_AST = null;
				tmp302_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp302_AST);
				match(K_IF);
				condition();
				astFactory.addASTChild(currentAST, returnAST);
				generation_scheme_AST = (AST)currentAST.root;
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
		returnAST = generation_scheme_AST;
	}
	
	public final void parameter_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST parameter_specification_AST = null;
		
		try {      // for error handling
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp303_AST = null;
			tmp303_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp303_AST);
			match(K_IN);
			discrete_range();
			astFactory.addASTChild(currentAST, returnAST);
			parameter_specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_107);
			} else {
			  throw ex;
			}
		}
		returnAST = parameter_specification_AST;
	}
	
	public final void generic_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST generic_list_AST = null;
		
		try {      // for error handling
			interface_list();
			astFactory.addASTChild(currentAST, returnAST);
			generic_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = generic_list_AST;
	}
	
	public final void group_constituent() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST group_constituent_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				astFactory.addASTChild(currentAST, returnAST);
				group_constituent_AST = (AST)currentAST.root;
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				astFactory.addASTChild(currentAST, returnAST);
				group_constituent_AST = (AST)currentAST.root;
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
		returnAST = group_constituent_AST;
	}
	
	public final void group_constituent_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST group_constituent_list_AST = null;
		
		try {      // for error handling
			group_constituent();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop276:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp304_AST = null;
					tmp304_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp304_AST);
					match(COMMA);
					group_constituent();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop276;
				}
				
			} while (true);
			}
			group_constituent_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = group_constituent_list_AST;
	}
	
	public final void signal_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signal_list_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			case STRING_LITERAL:
			{
				name();
				astFactory.addASTChild(currentAST, returnAST);
				{
				_loop544:
				do {
					if ((LA(1)==COMMA)) {
						AST tmp305_AST = null;
						tmp305_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp305_AST);
						match(COMMA);
						name();
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						break _loop544;
					}
					
				} while (true);
				}
				signal_list_AST = (AST)currentAST.root;
				break;
			}
			case K_OTHERS:
			{
				AST tmp306_AST = null;
				tmp306_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp306_AST);
				match(K_OTHERS);
				signal_list_AST = (AST)currentAST.root;
				break;
			}
			case K_ALL:
			{
				AST tmp307_AST = null;
				tmp307_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp307_AST);
				match(K_ALL);
				signal_list_AST = (AST)currentAST.root;
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
		returnAST = signal_list_AST;
	}
	
	public final void if_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST if_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp308_AST = null;
			tmp308_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp308_AST);
			match(K_IF);
			condition();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp309_AST = null;
			tmp309_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp309_AST);
			match(K_THEN);
			sequence_of_statements();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop287:
			do {
				if ((LA(1)==K_ELSIF)) {
					AST tmp310_AST = null;
					tmp310_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp310_AST);
					match(K_ELSIF);
					condition();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp311_AST = null;
					tmp311_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp311_AST);
					match(K_THEN);
					sequence_of_statements();
					astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp312_AST = null;
				tmp312_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp312_AST);
				match(K_ELSE);
				sequence_of_statements();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp313_AST = null;
			tmp313_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp313_AST);
			match(K_END);
			AST tmp314_AST = null;
			tmp314_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp314_AST);
			match(K_IF);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp315_AST = null;
			tmp315_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp315_AST);
			match(SEMI);
			if_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = if_statement_AST;
	}
	
	public final void incomplete_type_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST incomplete_type_declaration_AST = null;
		
		try {      // for error handling
			AST tmp316_AST = null;
			tmp316_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp316_AST);
			match(K_TYPE);
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp317_AST = null;
			tmp317_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp317_AST);
			match(SEMI);
			incomplete_type_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		returnAST = incomplete_type_declaration_AST;
	}
	
	public final void index_subtype_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST index_subtype_definition_AST = null;
		
		try {      // for error handling
			name();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp318_AST = null;
			tmp318_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp318_AST);
			match(K_RANGE);
			AST tmp319_AST = null;
			tmp319_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp319_AST);
			match(LSTGRT);
			index_subtype_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
		returnAST = index_subtype_definition_AST;
	}
	
	public final void interface_constant_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_constant_declaration_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_CONSTANT:
			{
				AST tmp320_AST = null;
				tmp320_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp320_AST);
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
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp321_AST = null;
			tmp321_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp321_AST);
			match(COLON);
			{
			switch ( LA(1)) {
			case K_IN:
			{
				AST tmp322_AST = null;
				tmp322_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp322_AST);
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
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				AST tmp323_AST = null;
				tmp323_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp323_AST);
				match(COLONEQ);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			interface_constant_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
		returnAST = interface_constant_declaration_AST;
	}
	
	public final void interface_signal_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_signal_declaration_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_SIGNAL:
			{
				AST tmp324_AST = null;
				tmp324_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp324_AST);
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
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp325_AST = null;
			tmp325_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp325_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_BUS:
			{
				AST tmp326_AST = null;
				tmp326_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp326_AST);
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
				AST tmp327_AST = null;
				tmp327_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp327_AST);
				match(COLONEQ);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			interface_signal_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
		returnAST = interface_signal_declaration_AST;
	}
	
	public final void interface_variable_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_variable_declaration_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case K_VARIABLE:
			{
				AST tmp328_AST = null;
				tmp328_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp328_AST);
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
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp329_AST = null;
			tmp329_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp329_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case COLONEQ:
			{
				AST tmp330_AST = null;
				tmp330_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp330_AST);
				match(COLONEQ);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			interface_variable_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
		returnAST = interface_variable_declaration_AST;
	}
	
	public final void interface_file_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_file_declaration_AST = null;
		
		try {      // for error handling
			AST tmp331_AST = null;
			tmp331_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp331_AST);
			match(K_FILE);
			identifier_list();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp332_AST = null;
			tmp332_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp332_AST);
			match(COLON);
			subtype_indication();
			astFactory.addASTChild(currentAST, returnAST);
			interface_file_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_88);
			} else {
			  throw ex;
			}
		}
		returnAST = interface_file_declaration_AST;
	}
	
	public final void interface_element() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST interface_element_AST = null;
		
		try {      // for error handling
			interface_declaration();
			astFactory.addASTChild(currentAST, returnAST);
			interface_element_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_108);
			} else {
			  throw ex;
			}
		}
		returnAST = interface_element_AST;
	}
	
	public final void mode() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST mode_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_IN:
			{
				AST tmp333_AST = null;
				tmp333_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp333_AST);
				match(K_IN);
				mode_AST = (AST)currentAST.root;
				break;
			}
			case K_OUT:
			{
				AST tmp334_AST = null;
				tmp334_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp334_AST);
				match(K_OUT);
				mode_AST = (AST)currentAST.root;
				break;
			}
			case K_INOUT:
			{
				AST tmp335_AST = null;
				tmp335_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp335_AST);
				match(K_INOUT);
				mode_AST = (AST)currentAST.root;
				break;
			}
			case K_BUFFER:
			{
				AST tmp336_AST = null;
				tmp336_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp336_AST);
				match(K_BUFFER);
				mode_AST = (AST)currentAST.root;
				break;
			}
			case K_LINKAGE:
			{
				AST tmp337_AST = null;
				tmp337_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp337_AST);
				match(K_LINKAGE);
				mode_AST = (AST)currentAST.root;
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
		returnAST = mode_AST;
	}
	
	public final void iteration_scheme() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST iteration_scheme_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_WHILE:
			{
				AST tmp338_AST = null;
				tmp338_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp338_AST);
				match(K_WHILE);
				condition();
				astFactory.addASTChild(currentAST, returnAST);
				iteration_scheme_AST = (AST)currentAST.root;
				break;
			}
			case K_FOR:
			{
				AST tmp339_AST = null;
				tmp339_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp339_AST);
				match(K_FOR);
				parameter_specification();
				astFactory.addASTChild(currentAST, returnAST);
				iteration_scheme_AST = (AST)currentAST.root;
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
		returnAST = iteration_scheme_AST;
	}
	
	public final void logical_name_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST logical_name_list_AST = null;
		
		try {      // for error handling
			logical_name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop340:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp340_AST = null;
					tmp340_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp340_AST);
					match(COMMA);
					logical_name();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop340;
				}
				
			} while (true);
			}
			logical_name_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = logical_name_list_AST;
	}
	
	public final void secondary_unit() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST secondary_unit_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ARCHITECTURE:
			{
				architecture_body();
				astFactory.addASTChild(currentAST, returnAST);
				secondary_unit_AST = (AST)currentAST.root;
				break;
			}
			case K_PACKAGE:
			{
				package_body();
				astFactory.addASTChild(currentAST, returnAST);
				secondary_unit_AST = (AST)currentAST.root;
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
		returnAST = secondary_unit_AST;
	}
	
	public final void primary_unit() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST primary_unit_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_ENTITY:
			{
				entity_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				primary_unit_AST = (AST)currentAST.root;
				break;
			}
			case K_CONFIGURATION:
			{
				configuration_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				primary_unit_AST = (AST)currentAST.root;
				break;
			}
			case K_PACKAGE:
			{
				package_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				primary_unit_AST = (AST)currentAST.root;
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
		returnAST = primary_unit_AST;
	}
	
	public final void literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST literal_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BIT_STRING_LITERAL:
			{
				bit_string_literal();
				astFactory.addASTChild(currentAST, returnAST);
				literal_AST = (AST)currentAST.root;
				break;
			}
			case K_NULL:
			{
				AST tmp341_AST = null;
				tmp341_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp341_AST);
				match(K_NULL);
				literal_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					literal_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==CHARACTER_LITERAL||LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (_tokenSet_2.member(LA(2)))) {
					enumeration_literal();
					astFactory.addASTChild(currentAST, returnAST);
					literal_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==STRING_LITERAL) && (_tokenSet_2.member(LA(2)))) {
					string_literal();
					astFactory.addASTChild(currentAST, returnAST);
					literal_AST = (AST)currentAST.root;
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
		returnAST = literal_AST;
	}
	
	public final void numeric_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST numeric_literal_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				numeric_literal_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_111.member(LA(1))) && (_tokenSet_105.member(LA(2)))) {
				physical_literal();
				astFactory.addASTChild(currentAST, returnAST);
				numeric_literal_AST = (AST)currentAST.root;
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
		returnAST = numeric_literal_AST;
	}
	
	public final void string_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST string_literal_AST = null;
		
		try {      // for error handling
			AST tmp342_AST = null;
			tmp342_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp342_AST);
			match(STRING_LITERAL);
			string_literal_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		returnAST = string_literal_AST;
	}
	
	public final void logical_name() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST logical_name_AST = null;
		
		try {      // for error handling
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			logical_name_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_112);
			} else {
			  throw ex;
			}
		}
		returnAST = logical_name_AST;
	}
	
	public final void logical_operator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST logical_operator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_AND:
			{
				AST tmp343_AST = null;
				tmp343_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp343_AST);
				match(K_AND);
				logical_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_OR:
			{
				AST tmp344_AST = null;
				tmp344_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp344_AST);
				match(K_OR);
				logical_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_NAND:
			{
				AST tmp345_AST = null;
				tmp345_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp345_AST);
				match(K_NAND);
				logical_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_NOR:
			{
				AST tmp346_AST = null;
				tmp346_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp346_AST);
				match(K_NOR);
				logical_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_XOR:
			{
				AST tmp347_AST = null;
				tmp347_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp347_AST);
				match(K_XOR);
				logical_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_XNOR:
			{
				AST tmp348_AST = null;
				tmp348_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp348_AST);
				match(K_XNOR);
				logical_operator_AST = (AST)currentAST.root;
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
		returnAST = logical_operator_AST;
	}
	
	public final void loop_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST loop_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp349_AST = null;
			tmp349_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp349_AST);
			match(K_LOOP);
			sequence_of_statements();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp350_AST = null;
			tmp350_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp350_AST);
			match(K_END);
			AST tmp351_AST = null;
			tmp351_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp351_AST);
			match(K_LOOP);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp352_AST = null;
			tmp352_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp352_AST);
			match(SEMI);
			loop_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = loop_statement_AST;
	}
	
	public final void miscellaneous_operator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST miscellaneous_operator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case STAR2:
			{
				AST tmp353_AST = null;
				tmp353_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp353_AST);
				match(STAR2);
				miscellaneous_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_ABS:
			{
				AST tmp354_AST = null;
				tmp354_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp354_AST);
				match(K_ABS);
				miscellaneous_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_NOT:
			{
				AST tmp355_AST = null;
				tmp355_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp355_AST);
				match(K_NOT);
				miscellaneous_operator_AST = (AST)currentAST.root;
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
		returnAST = miscellaneous_operator_AST;
	}
	
	public final void multiplying_operator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST multiplying_operator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case STAR:
			{
				AST tmp356_AST = null;
				tmp356_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp356_AST);
				match(STAR);
				multiplying_operator_AST = (AST)currentAST.root;
				break;
			}
			case SLASH:
			{
				AST tmp357_AST = null;
				tmp357_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp357_AST);
				match(SLASH);
				multiplying_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_MOD:
			{
				AST tmp358_AST = null;
				tmp358_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp358_AST);
				match(K_MOD);
				multiplying_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_REM:
			{
				AST tmp359_AST = null;
				tmp359_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp359_AST);
				match(K_REM);
				multiplying_operator_AST = (AST)currentAST.root;
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
		returnAST = multiplying_operator_AST;
	}
	
	public final Token  suffix() throws RecognitionException, TokenStreamException {
		Token tok;
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST suffix_AST = null;
		tok=null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				tok=simple_name();
				astFactory.addASTChild(currentAST, returnAST);
				suffix_AST = (AST)currentAST.root;
				break;
			}
			case CHARACTER_LITERAL:
			{
				character_literal();
				astFactory.addASTChild(currentAST, returnAST);
				suffix_AST = (AST)currentAST.root;
				break;
			}
			case STRING_LITERAL:
			{
				operator_symbol();
				astFactory.addASTChild(currentAST, returnAST);
				suffix_AST = (AST)currentAST.root;
				break;
			}
			case K_ALL:
			{
				AST tmp360_AST = null;
				tmp360_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp360_AST);
				match(K_ALL);
				suffix_AST = (AST)currentAST.root;
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
		returnAST = suffix_AST;
		return tok;
	}
	
	public final void next_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST next_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp361_AST = null;
			tmp361_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp361_AST);
			match(K_NEXT);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label();
				astFactory.addASTChild(currentAST, returnAST);
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
				AST tmp362_AST = null;
				tmp362_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp362_AST);
				match(K_WHEN);
				condition();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp363_AST = null;
			tmp363_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp363_AST);
			match(SEMI);
			next_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = next_statement_AST;
	}
	
	public final void null_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST null_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp364_AST = null;
			tmp364_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp364_AST);
			match(K_NULL);
			AST tmp365_AST = null;
			tmp365_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp365_AST);
			match(SEMI);
			null_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = null_statement_AST;
	}
	
	public final void physical_literal() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST physical_literal_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASED_LITERAL:
			case DECIMAL_LITERAL:
			{
				abstract_literal();
				astFactory.addASTChild(currentAST, returnAST);
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
			astFactory.addASTChild(currentAST, returnAST);
			physical_literal_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = physical_literal_AST;
	}
	
	public final void package_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST package_body_AST = null;
		
		try {      // for error handling
			AST tmp366_AST = null;
			tmp366_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp366_AST);
			match(K_PACKAGE);
			AST tmp367_AST = null;
			tmp367_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp367_AST);
			match(K_BODY);
			simple_name();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp368_AST = null;
			tmp368_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp368_AST);
			match(K_IS);
			package_body_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp369_AST = null;
			tmp369_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp369_AST);
			match(K_END);
			{
			switch ( LA(1)) {
			case K_PACKAGE:
			{
				AST tmp370_AST = null;
				tmp370_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp370_AST);
				match(K_PACKAGE);
				AST tmp371_AST = null;
				tmp371_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp371_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp372_AST = null;
			tmp372_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp372_AST);
			match(SEMI);
			package_body_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		returnAST = package_body_AST;
	}
	
	public final void package_body_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST package_body_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop384:
			do {
				if ((_tokenSet_113.member(LA(1)))) {
					package_body_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop384;
				}
				
			} while (true);
			}
			package_body_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = package_body_declarative_part_AST;
	}
	
	public final void package_body_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST package_body_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				package_body_declarative_item_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					package_body_declarative_item_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
					astFactory.addASTChild(currentAST, returnAST);
					package_body_declarative_item_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						package_body_declarative_item_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						group_template_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						package_body_declarative_item_AST = (AST)currentAST.root;
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
			returnAST = package_body_declarative_item_AST;
		}
		
	public final void package_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST package_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop395:
			do {
				if ((_tokenSet_115.member(LA(1)))) {
					package_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop395;
				}
				
			} while (true);
			}
			package_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = package_declarative_part_AST;
	}
	
	public final void package_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST package_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			case K_FUNCTION:
			case K_PURE:
			case K_IMPURE:
			{
				subprogram_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SIGNAL:
			{
				signal_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_COMPONENT:
			{
				component_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_DISCONNECT:
			{
				disconnection_specification();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				package_declarative_item_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					package_declarative_item_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
					attribute_declaration();
					astFactory.addASTChild(currentAST, returnAST);
					package_declarative_item_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						package_declarative_item_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						group_template_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						package_declarative_item_AST = (AST)currentAST.root;
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
			returnAST = package_declarative_item_AST;
		}
		
	public final void physical_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST physical_type_definition_AST = null;
		
		try {      // for error handling
			range_constraint();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp373_AST = null;
			tmp373_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp373_AST);
			match(K_UNITS);
			base_unit_declaration();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				secondary_unit_declaration();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp374_AST = null;
			tmp374_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp374_AST);
			match(K_END);
			AST tmp375_AST = null;
			tmp375_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp375_AST);
			match(K_UNITS);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				astFactory.addASTChild(currentAST, returnAST);
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
			physical_type_definition_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = physical_type_definition_AST;
	}
	
	public final void secondary_unit_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST secondary_unit_declaration_AST = null;
		
		try {      // for error handling
			identifier();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp376_AST = null;
			tmp376_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp376_AST);
			match(EQ);
			physical_literal();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp377_AST = null;
			tmp377_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp377_AST);
			match(SEMI);
			secondary_unit_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = secondary_unit_declaration_AST;
	}
	
	public final void port_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST port_list_AST = null;
		
		try {      // for error handling
			interface_list();
			astFactory.addASTChild(currentAST, returnAST);
			port_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = port_list_AST;
	}
	
	public final void procedure_call_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST procedure_call_statement_AST = null;
		
		try {      // for error handling
			{
			if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER||LA(1)==STRING_LITERAL) && (_tokenSet_117.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			procedure_call();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp378_AST = null;
			tmp378_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp378_AST);
			match(SEMI);
			procedure_call_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = procedure_call_statement_AST;
	}
	
	public final void process_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST process_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				process_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				process_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				process_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				process_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				process_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				process_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				process_declarative_item_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					process_declarative_item_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
					astFactory.addASTChild(currentAST, returnAST);
					process_declarative_item_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						process_declarative_item_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						process_declarative_item_AST = (AST)currentAST.root;
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
							astFactory.addASTChild(currentAST, returnAST);
							process_declarative_item_AST = (AST)currentAST.root;
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
							astFactory.addASTChild(currentAST, returnAST);
							process_declarative_item_AST = (AST)currentAST.root;
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
				returnAST = process_declarative_item_AST;
			}
			
	public final void process_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST process_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop430:
			do {
				if ((_tokenSet_119.member(LA(1)))) {
					process_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop430;
				}
				
			} while (true);
			}
			process_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
		returnAST = process_declarative_part_AST;
	}
	
	public final void sensitivity_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST sensitivity_list_AST = null;
		
		try {      // for error handling
			name();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop493:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp379_AST = null;
					tmp379_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp379_AST);
					match(COMMA);
					name();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop493;
				}
				
			} while (true);
			}
			sensitivity_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_120);
			} else {
			  throw ex;
			}
		}
		returnAST = sensitivity_list_AST;
	}
	
	public final void process_statement_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST process_statement_part_AST = null;
		
		try {      // for error handling
			{
			_loop440:
			do {
				if ((_tokenSet_62.member(LA(1)))) {
					sequential_statement();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop440;
				}
				
			} while (true);
			}
			process_statement_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = process_statement_part_AST;
	}
	
	public final void sequential_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST sequential_statement_AST = null;
		
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
				astFactory.addASTChild(currentAST, returnAST);
				sequential_statement_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					sequential_statement_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						sequential_statement_AST = (AST)currentAST.root;
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
							astFactory.addASTChild(currentAST, returnAST);
							sequential_statement_AST = (AST)currentAST.root;
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
								astFactory.addASTChild(currentAST, returnAST);
								sequential_statement_AST = (AST)currentAST.root;
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
									astFactory.addASTChild(currentAST, returnAST);
									sequential_statement_AST = (AST)currentAST.root;
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
										astFactory.addASTChild(currentAST, returnAST);
										sequential_statement_AST = (AST)currentAST.root;
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
											astFactory.addASTChild(currentAST, returnAST);
											sequential_statement_AST = (AST)currentAST.root;
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
												astFactory.addASTChild(currentAST, returnAST);
												sequential_statement_AST = (AST)currentAST.root;
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
													astFactory.addASTChild(currentAST, returnAST);
													sequential_statement_AST = (AST)currentAST.root;
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
														astFactory.addASTChild(currentAST, returnAST);
														sequential_statement_AST = (AST)currentAST.root;
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
															astFactory.addASTChild(currentAST, returnAST);
															sequential_statement_AST = (AST)currentAST.root;
														}
														else if ((_tokenSet_128.member(LA(1))) && (_tokenSet_130.member(LA(2)))) {
															signal_assignment_statement();
															astFactory.addASTChild(currentAST, returnAST);
															sequential_statement_AST = (AST)currentAST.root;
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
													returnAST = sequential_statement_AST;
												}
												
	public final void protected_type_body() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST protected_type_body_AST = null;
		
		try {      // for error handling
			AST tmp380_AST = null;
			tmp380_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp380_AST);
			match(K_PROTECTED);
			AST tmp381_AST = null;
			tmp381_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp381_AST);
			match(K_BODY);
			protected_type_body_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp382_AST = null;
			tmp382_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp382_AST);
			match(K_END);
			AST tmp383_AST = null;
			tmp383_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp383_AST);
			match(K_PROTECTED);
			AST tmp384_AST = null;
			tmp384_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp384_AST);
			match(K_BODY);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				astFactory.addASTChild(currentAST, returnAST);
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
			protected_type_body_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = protected_type_body_AST;
	}
	
	public final void protected_type_body_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST protected_type_body_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop452:
			do {
				if ((_tokenSet_119.member(LA(1)))) {
					protected_type_body_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop452;
				}
				
			} while (true);
			}
			protected_type_body_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = protected_type_body_declarative_part_AST;
	}
	
	public final void protected_type_body_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST protected_type_body_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_body_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_body_declarative_item_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					protected_type_body_declarative_item_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
					astFactory.addASTChild(currentAST, returnAST);
					protected_type_body_declarative_item_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						protected_type_body_declarative_item_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						protected_type_body_declarative_item_AST = (AST)currentAST.root;
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
							astFactory.addASTChild(currentAST, returnAST);
							protected_type_body_declarative_item_AST = (AST)currentAST.root;
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
							astFactory.addASTChild(currentAST, returnAST);
							protected_type_body_declarative_item_AST = (AST)currentAST.root;
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
				returnAST = protected_type_body_declarative_item_AST;
			}
			
	public final void protected_type_declaration() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST protected_type_declaration_AST = null;
		
		try {      // for error handling
			AST tmp385_AST = null;
			tmp385_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp385_AST);
			match(K_PROTECTED);
			protected_type_declarative_part();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp386_AST = null;
			tmp386_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp386_AST);
			match(K_END);
			AST tmp387_AST = null;
			tmp387_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp387_AST);
			match(K_PROTECTED);
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				simple_name();
				astFactory.addASTChild(currentAST, returnAST);
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
			protected_type_declaration_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = protected_type_declaration_AST;
	}
	
	public final void protected_type_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST protected_type_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop458:
			do {
				if ((_tokenSet_132.member(LA(1)))) {
					protected_type_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop458;
				}
				
			} while (true);
			}
			protected_type_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = protected_type_declarative_part_AST;
	}
	
	public final void protected_type_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST protected_type_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			case K_FUNCTION:
			case K_PURE:
			case K_IMPURE:
			{
				subprogram_specification();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ATTRIBUTE:
			{
				attribute_specification();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_declarative_item_AST = (AST)currentAST.root;
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
		returnAST = protected_type_declarative_item_AST;
	}
	
	public final void subprogram_specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subprogram_specification_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			{
				AST tmp388_AST = null;
				tmp388_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp388_AST);
				match(K_PROCEDURE);
				designator();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					AST tmp389_AST = null;
					tmp389_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp389_AST);
					match(LPAREN);
					formal_parameter_list();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp390_AST = null;
					tmp390_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp390_AST);
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
				subprogram_specification_AST = (AST)currentAST.root;
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
					AST tmp391_AST = null;
					tmp391_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp391_AST);
					match(K_PURE);
					break;
				}
				case K_IMPURE:
				{
					AST tmp392_AST = null;
					tmp392_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp392_AST);
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
				AST tmp393_AST = null;
				tmp393_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp393_AST);
				match(K_FUNCTION);
				designator();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case LPAREN:
				{
					AST tmp394_AST = null;
					tmp394_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp394_AST);
					match(LPAREN);
					formal_parameter_list();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp395_AST = null;
					tmp395_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp395_AST);
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
				AST tmp396_AST = null;
				tmp396_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp396_AST);
				match(K_RETURN);
				name();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_specification_AST = (AST)currentAST.root;
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
		returnAST = subprogram_specification_AST;
	}
	
	public final void protected_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST protected_type_definition_AST = null;
		
		try {      // for error handling
			if ((LA(1)==K_PROTECTED) && (_tokenSet_133.member(LA(2)))) {
				protected_type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_definition_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==K_PROTECTED) && (LA(2)==K_BODY)) {
				protected_type_body();
				astFactory.addASTChild(currentAST, returnAST);
				protected_type_definition_AST = (AST)currentAST.root;
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
		returnAST = protected_type_definition_AST;
	}
	
	public final void shift_expression() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST shift_expression_AST = null;
		
		try {      // for error handling
			simple_expression();
			astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
				simple_expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			shift_expression_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_135);
			} else {
			  throw ex;
			}
		}
		returnAST = shift_expression_AST;
	}
	
	public final void relational_operator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST relational_operator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case EQ:
			{
				AST tmp397_AST = null;
				tmp397_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp397_AST);
				match(EQ);
				relational_operator_AST = (AST)currentAST.root;
				break;
			}
			case SLASHEQ:
			{
				AST tmp398_AST = null;
				tmp398_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp398_AST);
				match(SLASHEQ);
				relational_operator_AST = (AST)currentAST.root;
				break;
			}
			case LST:
			{
				AST tmp399_AST = null;
				tmp399_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp399_AST);
				match(LST);
				relational_operator_AST = (AST)currentAST.root;
				break;
			}
			case LSTEQ:
			{
				AST tmp400_AST = null;
				tmp400_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp400_AST);
				match(LSTEQ);
				relational_operator_AST = (AST)currentAST.root;
				break;
			}
			case GRT:
			{
				AST tmp401_AST = null;
				tmp401_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp401_AST);
				match(GRT);
				relational_operator_AST = (AST)currentAST.root;
				break;
			}
			case GRTEQ:
			{
				AST tmp402_AST = null;
				tmp402_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp402_AST);
				match(GRTEQ);
				relational_operator_AST = (AST)currentAST.root;
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
		returnAST = relational_operator_AST;
	}
	
	public final void report_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST report_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp403_AST = null;
			tmp403_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp403_AST);
			match(K_REPORT);
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_SEVERITY:
			{
				AST tmp404_AST = null;
				tmp404_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp404_AST);
				match(K_SEVERITY);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp405_AST = null;
			tmp405_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp405_AST);
			match(SEMI);
			report_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = report_statement_AST;
	}
	
	public final void return_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST return_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp406_AST = null;
			tmp406_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp406_AST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp407_AST = null;
			tmp407_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp407_AST);
			match(SEMI);
			return_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = return_statement_AST;
	}
	
	public final void scalar_type_definition() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST scalar_type_definition_AST = null;
		
		try {      // for error handling
			if ((LA(1)==LPAREN)) {
				enumeration_type_definition();
				astFactory.addASTChild(currentAST, returnAST);
				scalar_type_definition_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					scalar_type_definition_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==K_RANGE) && (_tokenSet_10.member(LA(2)))) {
					physical_type_definition();
					astFactory.addASTChild(currentAST, returnAST);
					scalar_type_definition_AST = (AST)currentAST.root;
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
			returnAST = scalar_type_definition_AST;
		}
		
	public final void selected_waveforms() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST selected_waveforms_AST = null;
		
		try {      // for error handling
			waveform();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp408_AST = null;
			tmp408_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp408_AST);
			match(K_WHEN);
			choices();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop489:
			do {
				if ((LA(1)==COMMA)) {
					AST tmp409_AST = null;
					tmp409_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp409_AST);
					match(COMMA);
					waveform();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp410_AST = null;
					tmp410_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp410_AST);
					match(K_WHEN);
					choices();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop489;
				}
				
			} while (true);
			}
			selected_waveforms_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = selected_waveforms_AST;
	}
	
	public final void sensitivity_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST sensitivity_clause_AST = null;
		
		try {      // for error handling
			AST tmp411_AST = null;
			tmp411_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp411_AST);
			match(K_ON);
			sensitivity_list();
			astFactory.addASTChild(currentAST, returnAST);
			sensitivity_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_136);
			} else {
			  throw ex;
			}
		}
		returnAST = sensitivity_clause_AST;
	}
	
	public final void wait_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST wait_statement_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BASIC_IDENTIFIER:
			case EXTENDED_IDENTIFIER:
			{
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp412_AST = null;
			tmp412_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp412_AST);
			match(K_WAIT);
			{
			switch ( LA(1)) {
			case K_ON:
			{
				sensitivity_clause();
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
				astFactory.addASTChild(currentAST, returnAST);
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
			AST tmp413_AST = null;
			tmp413_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp413_AST);
			match(SEMI);
			wait_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = wait_statement_AST;
	}
	
	public final void variable_assignment_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST variable_assignment_statement_AST = null;
		
		try {      // for error handling
			{
			if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_128.member(LA(1))) && (_tokenSet_137.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			target();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp414_AST = null;
			tmp414_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp414_AST);
			match(COLONEQ);
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp415_AST = null;
			tmp415_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp415_AST);
			match(SEMI);
			variable_assignment_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = variable_assignment_statement_AST;
	}
	
	public final void signal_assignment_statement() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signal_assignment_statement_AST = null;
		
		try {      // for error handling
			{
			if ((LA(1)==BASIC_IDENTIFIER||LA(1)==EXTENDED_IDENTIFIER) && (LA(2)==COLON)) {
				label_colon();
				astFactory.addASTChild(currentAST, returnAST);
			}
			else if ((_tokenSet_128.member(LA(1))) && (_tokenSet_138.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			target();
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp416_AST = null;
			tmp416_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp416_AST);
			match(LSTEQ);
			{
			switch ( LA(1)) {
			case K_TRANSPORT:
			case K_REJECT:
			case K_INERTIAL:
			{
				delay_mechanism();
				astFactory.addASTChild(currentAST, returnAST);
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
			astFactory.addASTChild(currentAST, returnAST);
			AST tmp417_AST = null;
			tmp417_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp417_AST);
			match(SEMI);
			signal_assignment_statement_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		returnAST = signal_assignment_statement_AST;
	}
	
	public final void shift_operator() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST shift_operator_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_SLL:
			{
				AST tmp418_AST = null;
				tmp418_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp418_AST);
				match(K_SLL);
				shift_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_SRL:
			{
				AST tmp419_AST = null;
				tmp419_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp419_AST);
				match(K_SRL);
				shift_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_SLA:
			{
				AST tmp420_AST = null;
				tmp420_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp420_AST);
				match(K_SLA);
				shift_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_SRA:
			{
				AST tmp421_AST = null;
				tmp421_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp421_AST);
				match(K_SRA);
				shift_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_ROL:
			{
				AST tmp422_AST = null;
				tmp422_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp422_AST);
				match(K_ROL);
				shift_operator_AST = (AST)currentAST.root;
				break;
			}
			case K_ROR:
			{
				AST tmp423_AST = null;
				tmp423_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp423_AST);
				match(K_ROR);
				shift_operator_AST = (AST)currentAST.root;
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
		returnAST = shift_operator_AST;
	}
	
	public final void sign() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST sign_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case PLUS:
			{
				AST tmp424_AST = null;
				tmp424_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp424_AST);
				match(PLUS);
				sign_AST = (AST)currentAST.root;
				break;
			}
			case MINUS:
			{
				AST tmp425_AST = null;
				tmp425_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp425_AST);
				match(MINUS);
				sign_AST = (AST)currentAST.root;
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
		returnAST = sign_AST;
	}
	
	public final void signal_kind() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST signal_kind_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_REGISTER:
			{
				AST tmp426_AST = null;
				tmp426_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp426_AST);
				match(K_REGISTER);
				signal_kind_AST = (AST)currentAST.root;
				break;
			}
			case K_BUS:
			{
				AST tmp427_AST = null;
				tmp427_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp427_AST);
				match(K_BUS);
				signal_kind_AST = (AST)currentAST.root;
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
		returnAST = signal_kind_AST;
	}
	
	public final void term() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST term_AST = null;
		
		try {      // for error handling
			factor();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop586:
			do {
				if (((LA(1) >= STAR && LA(1) <= K_REM)) && (_tokenSet_12.member(LA(2)))) {
					multiplying_operator();
					astFactory.addASTChild(currentAST, returnAST);
					factor();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop586;
				}
				
			} while (true);
			}
			term_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		returnAST = term_AST;
	}
	
	public final void subprogram_declarative_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subprogram_declarative_part_AST = null;
		
		try {      // for error handling
			{
			_loop569:
			do {
				if ((_tokenSet_119.member(LA(1)))) {
					subprogram_declarative_item();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop569;
				}
				
			} while (true);
			}
			subprogram_declarative_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
		returnAST = subprogram_declarative_part_AST;
	}
	
	public final void subprogram_statement_part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subprogram_statement_part_AST = null;
		
		try {      // for error handling
			{
			_loop577:
			do {
				if ((_tokenSet_62.member(LA(1)))) {
					sequential_statement();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop577;
				}
				
			} while (true);
			}
			subprogram_statement_part_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		returnAST = subprogram_statement_part_AST;
	}
	
	public final void subprogram_kind() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subprogram_kind_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_PROCEDURE:
			{
				AST tmp428_AST = null;
				tmp428_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp428_AST);
				match(K_PROCEDURE);
				subprogram_kind_AST = (AST)currentAST.root;
				break;
			}
			case K_FUNCTION:
			{
				AST tmp429_AST = null;
				tmp429_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp429_AST);
				match(K_FUNCTION);
				subprogram_kind_AST = (AST)currentAST.root;
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
		returnAST = subprogram_kind_AST;
	}
	
	public final void subprogram_declarative_item() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST subprogram_declarative_item_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case K_TYPE:
			{
				type_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_SUBTYPE:
			{
				subtype_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_CONSTANT:
			{
				constant_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_VARIABLE:
			case K_SHARED:
			{
				variable_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_FILE:
			{
				file_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_ALIAS:
			{
				alias_declaration();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_declarative_item_AST = (AST)currentAST.root;
				break;
			}
			case K_USE:
			{
				use_clause();
				astFactory.addASTChild(currentAST, returnAST);
				subprogram_declarative_item_AST = (AST)currentAST.root;
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
					astFactory.addASTChild(currentAST, returnAST);
					subprogram_declarative_item_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_27.member(LA(1))) && (_tokenSet_28.member(LA(2)))) {
					subprogram_body();
					astFactory.addASTChild(currentAST, returnAST);
					subprogram_declarative_item_AST = (AST)currentAST.root;
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
						astFactory.addASTChild(currentAST, returnAST);
						subprogram_declarative_item_AST = (AST)currentAST.root;
					}
					else if ((LA(1)==K_ATTRIBUTE) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
						attribute_declaration();
						astFactory.addASTChild(currentAST, returnAST);
						subprogram_declarative_item_AST = (AST)currentAST.root;
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
							astFactory.addASTChild(currentAST, returnAST);
							subprogram_declarative_item_AST = (AST)currentAST.root;
						}
						else if ((LA(1)==K_GROUP) && (LA(2)==BASIC_IDENTIFIER||LA(2)==EXTENDED_IDENTIFIER)) {
							group_template_declaration();
							astFactory.addASTChild(currentAST, returnAST);
							subprogram_declarative_item_AST = (AST)currentAST.root;
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
				returnAST = subprogram_declarative_item_AST;
			}
			
	public final void timeout_clause() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST timeout_clause_AST = null;
		
		try {      // for error handling
			AST tmp430_AST = null;
			tmp430_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp430_AST);
			match(K_FOR);
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			timeout_clause_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		returnAST = timeout_clause_AST;
	}
	
	public final void waveform_element() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST waveform_element_AST = null;
		
		try {      // for error handling
			expression();
			astFactory.addASTChild(currentAST, returnAST);
			{
			switch ( LA(1)) {
			case K_AFTER:
			{
				AST tmp431_AST = null;
				tmp431_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp431_AST);
				match(K_AFTER);
				expression();
				astFactory.addASTChild(currentAST, returnAST);
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
			waveform_element_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_141);
			} else {
			  throw ex;
			}
		}
		returnAST = waveform_element_AST;
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
	
	protected void buildTokenTypeASTClassMap() {
		tokenTypeToASTClassMap=null;
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

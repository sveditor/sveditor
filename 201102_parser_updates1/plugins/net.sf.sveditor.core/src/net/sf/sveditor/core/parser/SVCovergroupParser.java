package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBCoverGroup.BinsKW;
import net.sf.sveditor.core.db.SVDBCoverPoint;
import net.sf.sveditor.core.db.SVDBCoverageOption;
import net.sf.sveditor.core.db.SVDBCoverpointBins;
import net.sf.sveditor.core.db.SVDBIdentifier;
import net.sf.sveditor.core.db.SVDBCoverpointBins.BinsType;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.SVDBLocation;

public class SVCovergroupParser extends SVParserBase {
	
	public SVCovergroupParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBCoverGroup parse() throws SVParseException {
		SVDBLocation start = lexer().getStartLocation();
		lexer().readKeyword("covergroup");
		String cg_name = lexer().readId();

		SVDBCoverGroup cg = new SVDBCoverGroup(cg_name);
		cg.setLocation(start);

		while (lexer().peekOperator("(")) {
			cg.setParamPort(parsers().tfPortListParser().parse());
		}

		if (lexer().peekOperator("@@")) {
			// block_event_expression
			error("block_event_expression not supported for covergroup sampling");
		} else if (lexer().peekOperator("@")) {
			cg.setCoverageEvent(parsers().exprParser().clocking_event());
		} else if (lexer().peekKeyword("with")) {
			// with function sample
			error("with_function_sample not supported for covergroup sampling");
		}
		
		lexer().readOperator(";");

		// Skip statements
		while (lexer().peek() != null && !lexer().peekKeyword("endgroup")) {
			ISVDBChildItem cov_item;
			
			if (lexer().peekKeyword("option", "type_option")) {
				cov_item = coverage_option();
			} else {
				cov_item = coverage_spec();
			}
			cg.addItem(cov_item);
		}
		
		cg.setEndLocation(lexer().getStartLocation());
		lexer().readKeyword("endgroup");
		
		if (lexer().peekOperator(":")) {
			lexer().eatToken();
			lexer().readId(); // labeled group
		}

		return cg;
	}
	
	private SVDBCoverageOption coverage_option() throws SVParseException {
		String type = lexer().readKeyword("option", "type_option");
		lexer().readOperator(".");
		String name = lexer().readId();
		
		SVDBCoverageOption opt = new SVDBCoverageOption(name, type.equals("type_option"));
		lexer().readOperator("=");
		opt.setExpr(parsers().exprParser().expression());
		
		return opt;
	}
	
	private ISVDBChildItem coverage_spec() throws SVParseException {
		ISVDBChildItem ret = null;
		String name = "";
		SVDBLocation start = lexer().getStartLocation();
		if (lexer().peekId()) {
			name = lexer().readId();
			lexer().readOperator(":");
		}
		
		String type = lexer().readKeyword("coverpoint", "cross");
		if (type.equals("coverpoint")) {
			SVDBCoverPoint cp = new SVDBCoverPoint(name);
			cp.setLocation(start);
			cover_point(cp);
			ret = cp;
		} else {
			SVDBCoverpointCross cp = new SVDBCoverpointCross(name);
			cp.setLocation(start);
			cover_cross(cp);
			ret = cp;
		}
		
		return ret;
	}
	
	private void cover_point(SVDBCoverPoint cp) throws SVParseException {
		cp.setTarget(parsers().exprParser().expression());
		
		if (lexer().peekKeyword("iff")) {
			lexer().eatToken();
			lexer().readOperator("(");
			cp.setIFF(parsers().exprParser().expression());
			lexer().readOperator(")");
		}
		
		if (lexer().peekOperator("{")) {
			lexer().eatToken();
			while (lexer().peek() != null && !lexer().peekOperator("}")) {
				if (lexer().peekKeyword("option", "type_option")) {
					cp.addItem(coverage_option());
				} else {
					boolean wildcard = lexer().peekKeyword("wildcard");
					if (wildcard) {
						lexer().eatToken();
					}
					
					String type = lexer().readKeyword("bins", "illegal_bins", "ignore_bins");
					BinsKW kw = (type.equals("bins"))?BinsKW.Bins:
						(type.equals("illegal_bins"))?BinsKW.IllegalBins:BinsKW.IgnoreBins;
					String id = lexer().readId();

					SVDBCoverpointBins bins = new SVDBCoverpointBins(wildcard, id, kw);

					boolean is_array = lexer().peekOperator("[");
					bins.setIsArray(is_array);
					if (is_array) {
						lexer().eatToken();
						if (lexer().peekOperator("]")) {
							lexer().eatToken();
						} else {
							bins.setArrayExpr(parsers().exprParser().expression());
						}
					}
					
					lexer().readOperator("=");
					
					if (lexer().peekKeyword("default")) {
						// Some sort of default bin
						lexer().eatToken();
						boolean is_sequence = lexer().peekKeyword("sequence");
						if (is_sequence) {
							lexer().eatToken();
							bins.setBinsType(BinsType.DefaultSeq);
						} else {
							bins.setBinsType(BinsType.Default);
						}
					} else {
						String op = lexer().readOperator("{", "(");
						if (op.equals("{")) {
							bins.setBinsType(BinsType.OpenRangeList);
						} else {
							bins.setBinsType(BinsType.TransList);
						}
					}
					
					if (lexer().peekKeyword("iff")) {
						lexer().eatToken();
						lexer().readOperator("(");
						bins.setIFF(parsers().exprParser().expression());
						lexer().readOperator(")");
					}
					cp.addItem(bins);
				}
				lexer().readOperator(";");
			}
			lexer().readOperator("}");
		} else {
			lexer().readOperator(";");
		}
	}
	
	private void cover_cross(SVDBCoverpointCross cp) throws SVParseException {
		while (lexer().peek() != null) {
			SVDBIdentifier id = SVDBIdentifier.readId(lexer());
			cp.getCoverpointList().add(id);
		
			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			} else {
				break;
			}
		}
		
		if (lexer().peekKeyword("iff")) {
			lexer().readOperator("(");
			cp.setIFF(parsers().exprParser().expression());
			lexer().readOperator(")");
		}
		
		if (lexer().peekOperator("{")) {
			while (lexer().peek() != null && !lexer().peekOperator("}")) {
				if (lexer().peekKeyword("option", "type_option")) {
					cp.addItem(coverage_option());
				} else {
					String type = lexer().readKeyword("bins", "illegal_bins", "ignore_bins");
					SVDBIdentifier id = readId();
					
				}
			}
		} else {
			lexer().readOperator(";");
		}
		
	}
}

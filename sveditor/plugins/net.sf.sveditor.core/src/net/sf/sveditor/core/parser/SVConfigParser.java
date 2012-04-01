package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBConfigDecl;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.stmt.SVDBConfigCellClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigDefaultClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigDesignStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigInstClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigRuleStmtBase;

public class SVConfigParser extends SVParserBase {

	public SVConfigParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse_config(ISVDBAddChildItem parent) throws SVParseException {
		SVDBConfigDecl cfg = new SVDBConfigDecl();
		cfg.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword("config");
		cfg.setName(fLexer.readId());
		fLexer.readOperator(";");
		parent.addChildItem(cfg);
		
		try {
			// local parameter declarations
			while (fLexer.peekKeyword("localparam")) {
				parsers().modIfcBodyItemParser().parse_parameter_decl(cfg);
			}

			// design_statement
			SVDBConfigDesignStmt design_stmt = new SVDBConfigDesignStmt();
			design_stmt.setLocation(fLexer.getStartLocation());
			fLexer.readKeyword("design");
			cfg.addChildItem(design_stmt);
			do {
				SVDBExpr id = fParsers.exprParser().hierarchical_identifier();
				design_stmt.addCellIdentifier(id);
			} while (fLexer.peekId());
			fLexer.readOperator(";");

			// config_rule_statement
			while (fLexer.peek() != null) {
				if (fLexer.peekKeyword("default")) {
					default_clause(cfg);
				} else if (fLexer.peekKeyword("instance")) {
					instance_clause(cfg);
				} else if (fLexer.peekKeyword("cell")) {
					cell_clause(cfg);
				} else {
					break;
				}
			}

			fLexer.readKeyword("endconfig");

			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
		} catch (SVParseException e) {
			cfg.setEndLocation(fLexer.getStartLocation());
			throw e;
		}
	}
	
	private void default_clause(ISVDBAddChildItem parent) throws SVParseException {
		SVDBConfigDefaultClauseStmt dflt_stmt = new SVDBConfigDefaultClauseStmt();
		dflt_stmt.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword("default");
		parent.addChildItem(dflt_stmt);
		
		fLexer.readKeyword("liblist");
		liblist_clause(dflt_stmt);
		
		fLexer.readOperator(";");
	}

	private void instance_clause(ISVDBAddChildItem parent) throws SVParseException {
		SVDBConfigInstClauseStmt inst_stmt = new SVDBConfigInstClauseStmt();
		
		inst_stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("instance");
		inst_stmt.setInstName(fParsers.exprParser().hierarchical_identifier());
		
		String type = fLexer.readKeyword("liblist","use");
		
		if (type.equals("liblist")) {
			liblist_clause(inst_stmt);
		} else {
			use_clause(inst_stmt);
		}
		
		fLexer.readOperator(";");
	}

	private void cell_clause(ISVDBAddChildItem parent) throws SVParseException {
		SVDBConfigCellClauseStmt inst_stmt = new SVDBConfigCellClauseStmt();
		
		inst_stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("cell");
		inst_stmt.setCellId(fParsers.exprParser().hierarchical_identifier());
		
		String type = fLexer.readKeyword("liblist","use");
		
		if (type.equals("liblist")) {
			liblist_clause(inst_stmt);
		} else {
			use_clause(inst_stmt);
		}
		
		fLexer.readOperator(";");
	}

	private void liblist_clause(SVDBConfigRuleStmtBase stmt) throws SVParseException {
		
		while (fLexer.peekId()) {
			stmt.addLib(fParsers.exprParser().idExpr());
		}
	}
	
	private void use_clause(SVDBConfigRuleStmtBase stmt) throws SVParseException {
		if (fLexer.peekId()) {
			stmt.setLibCellId(fParsers.exprParser().hierarchical_identifier());
		}
		
		if (fLexer.peekOperator("#")) {
			// parameter assignment(s)
			stmt.setParamAssign(fParsers.paramValueAssignParser().parse(true));
		}
		
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readKeyword("config");
		}
	}
}

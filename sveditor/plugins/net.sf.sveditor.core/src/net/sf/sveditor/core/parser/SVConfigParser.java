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
		
		fLexer.readKeyword(KW.CONFIG);
		cfg.setName(fLexer.readId());
		fLexer.readOperator(OP.SEMICOLON);
		parent.addChildItem(cfg);
		
		try {
			// local parameter declarations
			while (fLexer.peekKeyword(KW.LOCALPARAM)) {
				parsers().modIfcBodyItemParser().parse_parameter_decl(cfg);
			}

			// design_statement
			SVDBConfigDesignStmt design_stmt = new SVDBConfigDesignStmt();
			design_stmt.setLocation(fLexer.getStartLocation());
			fLexer.readKeyword(KW.DESIGN);
			cfg.addChildItem(design_stmt);
			do {
				SVDBExpr id = fParsers.exprParser().hierarchical_identifier();
				design_stmt.addCellIdentifier(id);
			} while (fLexer.peekId());
			fLexer.readOperator(OP.SEMICOLON);

			// config_rule_statement
			while (fLexer.peek() != null) {
				KW kw = fLexer.peekKeywordE();
				if (kw == KW.DEFAULT) {
					default_clause(cfg);
				} else if (kw == KW.INSTANCE) {
					instance_clause(cfg);
				} else if (kw == KW.CELL) {
					cell_clause(cfg);
				} else {
					break;
				}
			}

			fLexer.readKeyword(KW.ENDCONFIG);

			if (fLexer.peekOperator(OP.COLON)) {
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
		
		fLexer.readKeyword(KW.DEFAULT);
		parent.addChildItem(dflt_stmt);
		
		fLexer.readKeyword(KW.LIBLIST);
		liblist_clause(dflt_stmt);
		
		fLexer.readOperator(OP.SEMICOLON);
	}

	private void instance_clause(ISVDBAddChildItem parent) throws SVParseException {
		SVDBConfigInstClauseStmt inst_stmt = new SVDBConfigInstClauseStmt();
		
		inst_stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.INSTANCE);
		inst_stmt.setInstName(fParsers.exprParser().hierarchical_identifier());
		
		KW type = fLexer.readKeyword(KW.LIBLIST, KW.USE);
		
		if (type == KW.LIBLIST) {
			liblist_clause(inst_stmt);
		} else {
			use_clause(inst_stmt);
		}
		
		fLexer.readOperator(OP.SEMICOLON);
	}

	private void cell_clause(ISVDBAddChildItem parent) throws SVParseException {
		SVDBConfigCellClauseStmt inst_stmt = new SVDBConfigCellClauseStmt();
		
		inst_stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.CELL);
		inst_stmt.setCellId(fParsers.exprParser().hierarchical_identifier());
		
		KW type = fLexer.readKeyword(KW.LIBLIST, KW.USE);
		
		if (type == KW.LIBLIST) {
			liblist_clause(inst_stmt);
		} else {
			use_clause(inst_stmt);
		}
		
		fLexer.readOperator(OP.SEMICOLON);
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
		
		if (fLexer.peekOperator(OP.HASH)) {
			// parameter assignment(s)
			stmt.setParamAssign(fParsers.paramValueAssignParser().parse(true));
		}
		
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			fLexer.readKeyword(KW.CONFIG);
		}
	}
}

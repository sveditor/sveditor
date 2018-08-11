package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.expr.SVDBArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternRepeatExpr;
import net.sf.sveditor.core.db.expr.SVDBAssociativeArrayAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBAssociativeArrayElemAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBBinaryExpr;
import net.sf.sveditor.core.db.expr.SVDBCastExpr;
import net.sf.sveditor.core.db.expr.SVDBClockedPropertyExpr;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr;
import net.sf.sveditor.core.db.expr.SVDBConcatenationExpr;
import net.sf.sveditor.core.db.expr.SVDBCondExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverBinsExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverpointExpr;
import net.sf.sveditor.core.db.expr.SVDBCrossBinsSelectConditionExpr;
import net.sf.sveditor.core.db.expr.SVDBCtorExpr;
import net.sf.sveditor.core.db.expr.SVDBCycleDelayExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBFirstMatchExpr;
import net.sf.sveditor.core.db.expr.SVDBForeachLoopvarExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVDBIncDecExpr;
import net.sf.sveditor.core.db.expr.SVDBInsideExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.expr.SVDBMinTypMaxExpr;
import net.sf.sveditor.core.db.expr.SVDBNameMappedExpr;
import net.sf.sveditor.core.db.expr.SVDBNamedArgExpr;
import net.sf.sveditor.core.db.expr.SVDBNullExpr;
import net.sf.sveditor.core.db.expr.SVDBOpenRangeListExpr;
import net.sf.sveditor.core.db.expr.SVDBParamIdExpr;
import net.sf.sveditor.core.db.expr.SVDBPropertyCaseItem;
import net.sf.sveditor.core.db.expr.SVDBPropertyCaseStmt;
import net.sf.sveditor.core.db.expr.SVDBPropertyIfStmt;
import net.sf.sveditor.core.db.expr.SVDBPropertySpecExpr;
import net.sf.sveditor.core.db.expr.SVDBPropertyWeakStrongExpr;
import net.sf.sveditor.core.db.expr.SVDBRandomizeCallExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeDollarBoundExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeExpr;
import net.sf.sveditor.core.db.expr.SVDBRefElemExpr;
import net.sf.sveditor.core.db.expr.SVDBRefPathExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceClockingExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceCycleDelayExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceDistExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceMatchItemExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceRepetitionExpr;
import net.sf.sveditor.core.db.expr.SVDBStringExpr;
import net.sf.sveditor.core.db.expr.SVDBTFCallExpr;
import net.sf.sveditor.core.db.expr.SVDBTypeExpr;
import net.sf.sveditor.core.db.expr.SVDBUnaryExpr;
import net.sf.sveditor.core.db.stmt.SVDBActionBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssertStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssignStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssumeStmt;
import net.sf.sveditor.core.db.stmt.SVDBBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBBodyStmt;
import net.sf.sveditor.core.db.stmt.SVDBBreakStmt;
import net.sf.sveditor.core.db.stmt.SVDBCaseItem;
import net.sf.sveditor.core.db.stmt.SVDBCaseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigCellClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigDefaultClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigDesignStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigInstClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigRuleStmtBase;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListItem;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintForeachStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintIfStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintImplStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintSetStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintSolveBeforeStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintUniqueStmt;
import net.sf.sveditor.core.db.stmt.SVDBContinueStmt;
import net.sf.sveditor.core.db.stmt.SVDBCoverStmt;
import net.sf.sveditor.core.db.stmt.SVDBCoverageCrossBinsSelectStmt;
import net.sf.sveditor.core.db.stmt.SVDBCoverageOptionStmt;
import net.sf.sveditor.core.db.stmt.SVDBDefParamItem;
import net.sf.sveditor.core.db.stmt.SVDBDefParamStmt;
import net.sf.sveditor.core.db.stmt.SVDBDelayControlStmt;
import net.sf.sveditor.core.db.stmt.SVDBDisableForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBDisableStmt;
import net.sf.sveditor.core.db.stmt.SVDBDoWhileStmt;
import net.sf.sveditor.core.db.stmt.SVDBEventControlStmt;
import net.sf.sveditor.core.db.stmt.SVDBEventTriggerStmt;
import net.sf.sveditor.core.db.stmt.SVDBExportItem;
import net.sf.sveditor.core.db.stmt.SVDBExportStmt;
import net.sf.sveditor.core.db.stmt.SVDBExprStmt;
import net.sf.sveditor.core.db.stmt.SVDBFinalStmt;
import net.sf.sveditor.core.db.stmt.SVDBForStmt;
import net.sf.sveditor.core.db.stmt.SVDBForeachStmt;
import net.sf.sveditor.core.db.stmt.SVDBForeverStmt;
import net.sf.sveditor.core.db.stmt.SVDBForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBIfStmt;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBImportStmt;
import net.sf.sveditor.core.db.stmt.SVDBInitialStmt;
import net.sf.sveditor.core.db.stmt.SVDBLabeledStmt;
import net.sf.sveditor.core.db.stmt.SVDBNullStmt;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBProceduralContAssignStmt;
import net.sf.sveditor.core.db.stmt.SVDBRandseqProdStmt;
import net.sf.sveditor.core.db.stmt.SVDBRandseqStmt;
import net.sf.sveditor.core.db.stmt.SVDBRepeatStmt;
import net.sf.sveditor.core.db.stmt.SVDBReturnStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBTimePrecisionStmt;
import net.sf.sveditor.core.db.stmt.SVDBTimeUnitsStmt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem;
import net.sf.sveditor.core.db.stmt.SVDBWaitForkStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitOrderStmt;
import net.sf.sveditor.core.db.stmt.SVDBWaitStmt;
import net.sf.sveditor.core.db.stmt.SVDBWhileStmt;

public class SVDBVisitorBase implements ISVDBVisitor {
	
	@Override
	public void visit_action_block_stmt(SVDBActionBlockStmt s) {
		if (s.getStmt() != null) {
			s.getStmt().accept(this);
		}
		if (s.getElseStmt() != null) {
			s.getElseStmt().accept(this);
		}
	}
	
	@Override
	public void visit_always_stmt(SVDBAlwaysStmt s) {
		if (s.getAlwaysEvent() != null) {
			s.getAlwaysEvent().accept(this);
		}
	}

	
	@Override
	public void visit_alias(SVDBAlias a) {
		do_accept(a.getLvalue());
		for (SVDBExpr e : a.getAliases()) {
			e.accept(this);
		}
	}
	
	@Override
	public void visit_array_access_expr(SVDBArrayAccessExpr e) {
		if (e.getLhs() != null) {
			e.getLhs().accept(this);
		}
		if (e.getLow() != null) {
			e.getLow().accept(this);
		}
		if (e.getHigh() != null) {
			e.getHigh().accept(this);
		}
	}
	
	@Override
	public void visit_assert_stmt(SVDBAssertStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		if (s.getDelay() != null) {
			s.getDelay().accept(this);
		}
		if (s.getActionBlock() != null) {
			s.getActionBlock().accept(this);
		}
	}

	@Override
	public void visit_assign_expr(SVDBAssignExpr e) {
		e.getLhs().accept(this);
		e.getRhs().accept(this);
	}
	
	@Override
	public void visit_assignment_pattern_expr(SVDBAssignmentPatternExpr e) {
		for (SVDBExpr p : e.getPatternList()) {
			p.accept(this);
		}
	}
	
	@Override
	public void visit_assignment_pattern_repeat_expr(SVDBAssignmentPatternRepeatExpr e) {
		e.getRepeatExpr().accept(this);
		visit_assignment_pattern_expr(e);
	}

	@Override
	public void visit_assign(SVDBAssign a) {
		for (SVDBAssignItem i : a.getAssignList()) {
			i.accept(this);
		}
	}

	@Override
	public void visit_assign_item(SVDBAssignItem a) {
		do_accept(a.getLHS(), a.getRHS());
	}
	
	@Override
	public void visit_assign_stmt(SVDBAssignStmt s) {
		if (s.getLHS() != null) {
			s.getLHS().accept(this);
		}
		if (s.getDelayExpr() != null) {
			s.getDelayExpr().accept(this);
		}
		if (s.getRHS() != null) {
			s.getRHS().accept(this);
		}
	}
	
	@Override
	public void visit_associative_array_assign_expr(SVDBAssociativeArrayAssignExpr e) {
		for (SVDBAssociativeArrayElemAssignExpr el : e.getElements()) {
			el.accept(this);
		}
	}

	@Override
	public void visit_associative_array_elem_assign_expr(SVDBAssociativeArrayElemAssignExpr e) {
		if (e.getKey() != null) {
			e.getKey().accept(this);
		}
		if (e.getValue() != null) {
			e.getValue().accept(this);
		}
	}
	
	@Override
	public void visit_assume_stmt(SVDBAssumeStmt s) {
		visit_assert_stmt(s);
	}

	@Override
	public void visit_binary_expr(SVDBBinaryExpr e) {
		e.getLhs().accept(this);
		e.getRhs().accept(this);
	}

	@Override
	public void visit_bind(SVDBBind b) {
		do_accept(
				b.getTargetTypeName(),
				b.getBindInst());
		
		for (SVDBExpr e : b.getTargetInstNameList()) {
			e.accept(this);
		}
	}
	
	protected void visit_body_stmt(SVDBBodyStmt s) {
		for (ISVDBChildItem c : s.getChildren()) {
			c.accept(this);
		}
	}
	
	@Override
	public void visit_block_stmt(SVDBBlockStmt s) {
		for (ISVDBChildItem c : s.getChildren()) {
			c.accept(this);
		}
	}
	
	@Override
	public void visit_break_stmt(SVDBBreakStmt s) {
		
	}
	
	@Override
	public void visit_type_info_builtin(SVDBTypeInfoBuiltin t) {
		
	}
	
	@Override
	public void visit_case_item(SVDBCaseItem s) {
		for (SVDBExpr e : s.getExprList()) {
			e.accept(this);
		}
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_case_stmt(SVDBCaseStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		for (SVDBCaseItem i : s.getCaseItemList()) {
			i.accept(this);
		}
	}
	
	@Override
	public void visit_cast_expr(SVDBCastExpr e) {
		if (e.getCastType() != null) {
			e.getCastType().accept(this);
		}
		e.getExpr().accept(this);
	}

	@Override
	public void visit_class_decl(SVDBClassDecl c) {
		do_accept(c.getClassType());
		
		for (SVDBModIfcClassParam p : c.getParameters()) {
			p.accept(this);
		}
		
		for (SVDBTypeInfoClassType t : c.getSuperClassList()) {
			t.accept(this);
		}
		for (SVDBTypeInfoClassType i : c.getImplements()) {
			i.accept(this);
		}

		// Visit the sub-items
		visit_scope(c);
	}

	@Override
	public void visit_clocked_property_expr(SVDBClockedPropertyExpr e) {
		if (e.getClockingExpr() != null) {
			e.getClockingExpr().accept(this);
		}
		
		if (e.getPropertyExpr() != null) {
			e.getPropertyExpr().accept(this);
		}
	}

	@Override
	public void visit_clocking_block(SVDBClockingBlock b) {
		do_accept(b.getExpr());
		
		visit_scope(b);
	}
	
	
	@Override
	public void visit_clocking_event_expr(SVDBClockingEventExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_concatenation_expr(SVDBConcatenationExpr e) {
		for (SVDBExpr el : e.getElements()) {
			el.accept(this);
		}
	}

	@Override
	public void visit_cond_expr(SVDBCondExpr e) {
		if (e.getLhs() != null) {
			e.getLhs().accept(this);
		}
		if (e.getMhs() != null) {
			e.getMhs().accept(this);
		}
		if (e.getRhs() != null) {
			e.getRhs().accept(this);
		}
	}
	
	@Override
	public void visit_config_decl(SVDBConfigDecl c) {
		visit_scope(c);
	}
	
	protected void visit_config_rule_stmt_base(SVDBConfigRuleStmtBase s) {
		for (SVDBExpr e : s.getLibUseList()) {
			e.accept(this);
		}
		do_accept(s.getLibCellId());
	}
	
	@Override
	public void visit_config_cell_clause_stmt(SVDBConfigCellClauseStmt s) {
		do_accept(s.getCellId());
		visit_config_rule_stmt_base(s);
	}
	
	@Override
	public void visit_config_default_clause_stmt(SVDBConfigDefaultClauseStmt s) {
		visit_config_rule_stmt_base(s);
	}
	
	@Override
	public void visit_config_design_stmt(SVDBConfigDesignStmt s) {
		for (SVDBExpr e : s.getCellIdentifiers()) {
			e.accept(this);
		}
	}
	
	@Override
	public void visit_config_inst_clause_stmt(SVDBConfigInstClauseStmt s) {
		do_accept(s.getInstName());
		
		visit_config_rule_stmt_base(s);
	}
	
	@Override
	public void visit_constraint(SVDBConstraint c) {
		visit_scope(c);
	}
	
	@Override
	public void visit_constraint_dist_list_item(SVDBConstraintDistListItem i) {
		if (i.getLHS() != null) {
			i.getLHS().accept(this);
		}
		if (i.getRHS() != null) {
			i.getRHS().accept(this);
		}
	}
	
	@Override
	public void visit_constraint_dist_list_stmt(SVDBConstraintDistListStmt s) {
		for (SVDBExpr l : s.getLHS()) {
			l.accept(this);
		}
		for (SVDBConstraintDistListItem i : s.getDistItems()) {
			i.accept(this);
		}
	}
	
	@Override
	public void visit_constraint_foreach_stmt(SVDBConstraintForeachStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		if (s.getStmt() != null) {
			s.getStmt().accept(this);
		}
	}
	
	@Override
	public void visit_constraint_if_stmt(SVDBConstraintIfStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		if (s.getConstraint() != null) {
			s.getConstraint().accept(this);
		}
		if (s.getElseClause() != null) {
			s.getElseClause().accept(this);
		}
	}
	
	@Override
	public void visit_constraint_impl_stmt(SVDBConstraintImplStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		if (s.getConstraintSet() != null) {
			s.getConstraintSet().accept(this);
		}
	}
	
	@Override
	public void visit_constraint_set_stmt(SVDBConstraintSetStmt s) {
		for (SVDBStmt c : s.getConstraintList()) {
			c.accept(this);
		}
	}
	
	@Override
	public void visit_constraint_solve_before_stmt(SVDBConstraintSolveBeforeStmt s) {
		for (SVDBExpr e : s.getSolveBeforeList()) {
			e.accept(this);
		}
		for (SVDBExpr e : s.getSolveAfterList()) {
			e.accept(this);
		}
	}
	
	@Override
	public void visit_constraint_unique_stmt(SVDBConstraintUniqueStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_continue_stmt(SVDBContinueStmt s) {
		
	}

	@Override
	public void visit_cover_bins_expr(SVDBCoverBinsExpr e) {
		do_accept(e.getArrayExpr());
		
		for (SVDBExpr r : e.getRangeList()) {
			r.accept(this);
		}
	}
	
	@Override
	public void visit_cover_stmt(SVDBCoverStmt s) {
		visit_assert_stmt(s);
	}
	
	@Override
	public void visit_cover_cross_bin_sel(SVDBCoverCrossBinsSel s) {
		do_accept(s.getSelectExpr());
	}
	
	@Override
	public void visit_coverage_cross_bins_select_stmt(SVDBCoverageCrossBinsSelectStmt s) {
		if (s.getBinsName() != null) {
			s.getBinsName().accept(this);
		}
		if (s.getSelectCondition() != null) {
			s.getSelectCondition().accept(this);
		}
		if (s.getIffExpr() != null) {
			s.getIffExpr().accept(this);
		}
	}
	
	@Override
	public void visit_coverage_option_stmt(SVDBCoverageOptionStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_covergroup(SVDBCovergroup c) {
		do_accept(c.getCoverageEvent());
		for (SVDBParamPortDecl p : c.getParamPort()) {
			p.accept(this);
		}
		visit_scope(c);
	}
	
	@Override
	public void visit_coverpoint(SVDBCoverpoint c) {
		do_accept(c.getTarget(), c.getIFF());
		visit_scope(c);
	}
	
	@Override
	public void visit_coverpoint_bins(SVDBCoverpointBins b) {
		do_accept(b.getArrayExpr(), b.getIFF(), b.getWith());
	}
	
	@Override
	public void visit_coverpoint_cross(SVDBCoverpointCross c) {
		for (SVDBIdentifierExpr i : c.getCoverpointList()) {
			i.accept(this);
		}
		do_accept(c.getIFF());
	
		visit_scope(c);
	}
	
	@Override
	public void visit_coverpoint_expr(SVDBCoverpointExpr e) {
		if (e.getTarget() != null) {
			e.getTarget().accept(this);
		}
		
		if (e.getIFFExpr() != null) {
			e.getIFFExpr().accept(this);
		}
		
		for (SVDBCoverBinsExpr b : e.getCoverBins()) {
			b.accept(this);
		}
	}

	@Override
	public void visit_cross_bins_select_conditional_expr(SVDBCrossBinsSelectConditionExpr e) {
		if (e.getBinsExpr() != null) {
			e.getBinsExpr().accept(this);
		}
		
		for (SVDBExpr i : e.getIntersectList()) {
			i.accept(this);
		}
	}
	
	@Override
	public void visit_ctor_expr(SVDBCtorExpr e) {
		for (SVDBExpr a : e.getArgs()) {
			a.accept(this);
		}
	}
	
	@Override
	public void visit_cycle_delay_expr(SVDBCycleDelayExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_def_param_item(SVDBDefParamItem i) {
		if (i.getTarget() != null) {
			i.getTarget().accept(this);
		}
		if (i.getExpr() != null) {
			i.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_def_param_stmt(SVDBDefParamStmt s) {
		for (SVDBDefParamItem i : s.getParamAssignList()) {
			i.accept(this);
		}
	}
	
	@Override
	public void visit_delay_control_stmt(SVDBDelayControlStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_disable_fork_stmt(SVDBDisableForkStmt s) {
		visit_disable_stmt(s);
	}
	
	@Override
	public void visit_disable_stmt(SVDBDisableStmt s) {
		if (s.getHierarchicalId() != null) {
			s.getHierarchicalId().accept(this);
		}
	}
	
	@Override
	public void visit_do_while_stmt(SVDBDoWhileStmt s) {
		if (s.getCond() != null) {
			s.getCond().accept(this);
		}
	
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_doc_comment(SVDBDocComment c) {
		
	}
	
	@Override
	public void visit_event_control_stmt(SVDBEventControlStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_event_trigger_stmt(SVDBEventTriggerStmt s) {
		if (s.getDelayOrEventControl() != null) {
			s.getDelayOrEventControl().accept(this);
		}
		if (s.getHierarchicalEventIdentifier() != null) {
			s.getHierarchicalEventIdentifier().accept(this);
		}
	}
	
	@Override
	public void visit_export_item(SVDBExportItem i) {
		
	}
	
	@Override
	public void visit_export_stmt(SVDBExportStmt s) {
		visit_scope(s);
	}
	
	@Override
	public void visit_expr_stmt(SVDBExprStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
	}

	@Override
	public void visit_field_access_expr(SVDBFieldAccessExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
		if (e.getLeaf() != null) {
			e.getLeaf().accept(this);
		}
	}
	
	@Override
	public void visit_file(SVDBFile f) {
		visit_scope(f);
	}
	
	@Override
	public void visit_final_stmt(SVDBFinalStmt s) {
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_first_match_expr(SVDBFirstMatchExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
		
		for (SVDBExpr m : e.getSequenceMatchItems()) {
			m.accept(this);
		}
	}
	
	@Override
	public void visit_foreach_loopvar_expr(SVDBForeachLoopvarExpr e) {
		if (e.getId() != null) {
			e.getId().accept(this);
		}
		for (SVDBExpr l : e.getLoopVarList()) {
			l.accept(this);
		}
	}
	
	@Override
	public void visit_foreach_stmt(SVDBForeachStmt s) {
		if (s.getCond() != null) {
			s.getCond().accept(this);
		}
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_forever_stmt(SVDBForeverStmt s) {
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_fork_stmt(SVDBForkStmt s) {
		visit_block_stmt(s);
	}
	
	@Override
	public void visit_for_stmt(SVDBForStmt s) {
		if (s.getInitStmt() != null) {
			s.getInitStmt().accept(this);
		}
		if (s.getTestExpr() != null) {
			s.getTestExpr().accept(this);
		}
		if (s.getIncrStmt() != null) {
			s.getIncrStmt().accept(this);
		}
		visit_body_stmt(s);
	}

	@Override
	public void visit_function_decl(SVDBFunction f) {
		if (f.getReturnType() != null) {
			f.getReturnType().accept(this);
		}
		
		for (SVDBParamPortDecl p : f.getParams()) {
			p.accept(this);
		}

		// Visit the function body
		visit_scope(f);
	}
	
	@Override
	public void visit_generate_block(SVDBGenerateBlock b) {
		visit_scope(b);
	}
	
	@Override
	public void visit_generate_for(SVDBGenerateFor g) {
		// TODO:
	}
	
	@Override
	public void visit_generate_if(SVDBGenerateIf g) {
		do_accept(g.getExpr(), g.getIfBody(), g.getElseBody());
	}
	
	@Override
	public void visit_generate_region(SVDBGenerateRegion g) {
		visit_scope(g);
	}
	
	@Override
	public void visit_identifier_expr(SVDBIdentifierExpr e) {
		
	}
	
	@Override
	public void visit_if_stmt(SVDBIfStmt s) {
		do_accept(s.getCond(), s.getIfStmt(), s.getElseStmt());
	}

	@Override
	public void visit_inc_dec_expr(SVDBIncDecExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_include(SVDBInclude i) {
		
	}
	
	@Override
	public void visit_import_item(SVDBImportItem i) {
		
	}
	
	@Override
	public void visit_import_stmt(SVDBImportStmt s) {
		visit_scope(s);
	}
	
	@Override
	public void visit_interface_decl(SVDBInterfaceDecl i) {
		visit_mod_ifc_decl(i);
	}
	
	@Override
	public void visit_initial_stmt(SVDBInitialStmt s) {
		visit_body_stmt(s);
	}

	@Override
	public void visit_inside_expr(SVDBInsideExpr e) {
		if (e.getLhs() != null) {
			e.getLhs().accept(this);
		}
		for (SVDBExpr v : e.getValueRangeList()) {
			v.accept(this);
		}
	}
	
	@Override
	public void visit_labeled_stmt(SVDBLabeledStmt s) {
		visit_body_stmt(s);
	}

	@Override
	public void visit_literal_expr(SVDBLiteralExpr e) {
		
	}

	@Override
	public void visit_min_typ_max_expr(SVDBMinTypMaxExpr e) {
		if (e.getMin() != null) {
			e.getMin().accept(this);
		}
		if (e.getTyp() != null) {
			e.getTyp().accept(this);
		}
		if (e.getMax() != null) {
			e.getMax().accept(this);
		}
	}
	
	@Override
	public void visit_macro_def(SVDBMacroDef d) {
		for (SVDBMacroDefParam p : d.getParameters()) {
			p.accept(this);
		}
	}
	
	@Override
	public void visit_macro_def_param(SVDBMacroDefParam d) {
		
	}
	
	@Override
	public void visit_marker(SVDBMarker m) {
		
	}
	
	@Override
	public void visit_mod_ifc_class_param(SVDBModIfcClassParam p) {
		do_accept(p.getDefaultType(), p.getDefault());
		
	}

	@Override
	public void visit_mod_ifc_decl(SVDBModIfcDecl d) {
		for (SVDBModIfcClassParam p : d.getParameters()) {
			p.accept(this);
		}
		for (SVDBParamPortDecl p : d.getPorts()) {
			p.accept(this);
		}
	}
	
	@Override
	public void visit_mod_ifc_inst(SVDBModIfcInst i) {
		do_accept(i.getTypeInfo());
		
		for (SVDBModIfcInstItem it : i.getInstList()) {
			it.accept(this);
		}
	}
	
	@Override
	public void visit_mod_ifc_inst_item(SVDBModIfcInstItem i) {
		for (SVDBVarDimItem it : i.getArrayDim()) {
			it.accept(this);
		}
		i.getPortMap().accept(this);
	}
	
	@Override
	public void visit_modport_clocking_port_decl(SVDBModportClockingPortDecl p) {
		visit_modport_ports_decl(p);
	}
	
	@Override
	public void visit_modport_decl(SVDBModportDecl p) {
		visit_scope(p);
	}
	
	@Override
	public void visit_modport_item(SVDBModportItem i) {
		for (SVDBModportPortsDecl p : i.getPortsList()) {
			p.accept(this);
		}
	}
	
	protected void visit_modport_ports_decl(SVDBModportPortsDecl p) {
		for (ISVDBChildItem c : p.getPorts()) {
			c.accept(this);
		}
	}
	
	@Override
	public void visit_modport_simple_port(SVDBModportSimplePort p) {
		do_accept(p.getExpr());
	}
	
	@Override
	public void visit_modport_simple_ports_decl(SVDBModportSimplePortsDecl p) {
		for (SVDBModportSimplePort sp : p.getPortList()) {
			sp.accept(this);
		}
	
		visit_modport_ports_decl(p);
	}
	
	@Override
	public void visit_modport_tf_port(SVDBModportTFPort p) {
		do_accept(p.getPrototype());
	}
	
	@Override
	public void visit_modport_tf_ports_decl(SVDBModportTFPortsDecl d) {
		visit_modport_ports_decl(d);
	}
	
	@Override
	public void visit_module_decl(SVDBModuleDecl d) {
		visit_mod_ifc_decl(d);
	}

	@Override
	public void visit_named_arg_expr(SVDBNamedArgExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_name_mapped_expr(SVDBNameMappedExpr e) {
		if (e.getName() != null) {
			e.getName().accept(this);
		}
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}

	@Override
	public void visit_null_expr(SVDBNullExpr e) {
		
	}
	
	@Override
	public void visit_null_stmt(SVDBNullStmt s) {
		
	}

	@Override
	public void visit_open_range_list_expr(SVDBOpenRangeListExpr e) {
		for (SVDBExpr r : e.getRangeList()) {
			r.accept(this);
		}
	}

	@Override
	public void visit_package_decl(SVDBPackageDecl p) {
		visit_scope(p);
	}

	@Override
	public void visit_param_id_expr(SVDBParamIdExpr e) {
		if (e.getParamExpr() != null) {
			e.getParamExpr().accept(this);
		}
	}
	
	@Override
	public void visit_param_port_decl(SVDBParamPortDecl d) {
		visit_var_decl_stmt(d);
	}
	
	@Override
	public void visit_param_value_assign(SVDBParamValueAssign a) {
		do_accept(a.getValue(), a.getTypeInfo());
	}
	
	@Override
	public void visit_param_value_assign_list(SVDBParamValueAssignList l) {
		for (SVDBParamValueAssign a : l.getParameters()) {
			a.accept(this);
		}
	}
	
	@Override
	public void visit_procedural_cont_assign_stmt(SVDBProceduralContAssignStmt s) {
		do_accept(s.getExpr());
	}
	
	@Override
	public void visit_program_decl(SVDBProgramDecl p) {
		visit_mod_ifc_decl(p);
	}
	
	@Override
	public void visit_property(SVDBProperty p) {
		do_accept(p.getExpr());
		for (SVDBParamPortDecl pp : p.getPropertyPortList()) {
			pp.accept(this);
		}
		visit_scope(p);
	}
	
	@Override
	public void visit_property_case_item(SVDBPropertyCaseItem i) {
		for (SVDBExpr e : i.getExprList()) {
			e.accept(this);
		}
		if (i.getStmt() != null) {
			i.getStmt().accept(this);
		}
	}
	
	@Override
	public void visit_property_case_stmt(SVDBPropertyCaseStmt s) {
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		for (SVDBPropertyCaseItem i : s.getItemList()) {
			i.accept(this);
		}
	}
	
	@Override
	public void visit_property_if_stmt(SVDBPropertyIfStmt s) {
		if (s.getIfExpr() != null) {
			s.getIfExpr().accept(this);
		}
		if (s.getExpr() != null) {
			s.getExpr().accept(this);
		}
		if (s.getElseExpr() != null) {
			s.getElseExpr().accept(this);
		}
	}
	
	@Override
	public void visit_property_spec_expr(SVDBPropertySpecExpr e) {
		if (e.getClockingEvent() != null) {
			e.getClockingEvent().accept(this);
		}
		if (e.getDisableExpr() != null) {
			e.getDisableExpr().accept(this);
		}
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_property_weak_strong_expr(SVDBPropertyWeakStrongExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_randomize_call_expr(SVDBRandomizeCallExpr e) {
		visit_tf_call_expr(e);
		if (e.getWithBlock() != null) {
			e.getWithBlock().accept(this);
		}
	}
	
	@Override
	public void visit_randseq_stmt(SVDBRandseqStmt s) {
		for (SVDBParamPortDecl p : s.getTfPortList()) {
			p.accept(this);
		}
		for (SVDBRandseqProdStmt p : s.getProductions()) {
			p.accept(this);
		}
	}
	
	@Override
	public void visit_randseq_prod_stmt(SVDBRandseqProdStmt s) {
		do_accept(s.getRetType());
		// TODO:
	}
	
	@Override
	public void visit_range_dollar_bound_expr(SVDBRangeDollarBoundExpr e) {
		
	}
	
	@Override
	public void visit_range_expr(SVDBRangeExpr e) {
		if (e.getLeft() != null) {
			e.getLeft().accept(this);
		}
		if (e.getRight() != null) {
			e.getRight().accept(this);
		}
	}
	
	@Override
	public void visit_ref_elem_expr(SVDBRefElemExpr e) {
		// TODO Auto-generated method stub
		
	}
	
	@Override
	public void visit_ref_path_expr(SVDBRefPathExpr e) {
		// TODO Auto-generated method stub
		
	}
	
	@Override
	public void visit_repeat_stmt(SVDBRepeatStmt s) {
		do_accept(s.getExpr());
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_return_stmt(SVDBReturnStmt s) {
		do_accept(s.getExpr());
	}
	
	@Override
	public void visit_sequence(SVDBSequence s) {
		do_accept(s.getExpr());
		for (SVDBParamPortDecl p : s.getPortList()) {
			p.accept(this);
		}
		for (SVDBVarDeclStmt v : s.getVarDeclList()) {
			v.accept(this);
		}
	}
	
	@Override
	public void visit_sequence_clocking_expr(SVDBSequenceClockingExpr e) {
		if (e.getClockingExpr() != null) {
			e.getClockingExpr().accept(this);
		}
		if (e.getSequenceExpr() != null) {
			e.getSequenceExpr().accept(this);
		}
	}
	
	@Override
	public void visit_sequence_cycle_delay_expr(SVDBSequenceCycleDelayExpr e) {
		if (e.getLhs() != null) {
			e.getLhs().accept(this);
		}
		if (e.getDelay() != null) {
			e.getDelay().accept(this);
		}
		if (e.getRhs() != null) {
			e.getRhs().accept(this);
		}
	}
	
	@Override
	public void visit_sequence_dist_expr(SVDBSequenceDistExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
		if (e.getDistExpr() != null) {
			e.getDistExpr().accept(this);
		}
	}
	
	@Override
	public void visit_sequence_match_item_expr(SVDBSequenceMatchItemExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
		for (SVDBExpr i : e.getMatchItemExprList()) {
			i.accept(this);
		}
	}
	
	@Override
	public void visit_sequence_repetition_expr(SVDBSequenceRepetitionExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}
	
	@Override
	public void visit_string_expr(SVDBStringExpr e) {
		
	}
	
	@Override
	public void visit_task(SVDBTask t) {
		for (SVDBParamPortDecl p : t.getParams()) {
			p.accept(this);
		}
		visit_scope(t);
	}
	
	@Override
	public void visit_tf_call_expr(SVDBTFCallExpr e) {
		if (e.getTarget() != null) {
			e.getTarget().accept(this);
		}
		for (SVDBExpr a : e.getArgs()) {
			a.accept(this);
		}
		if (e.getWithExpr() != null) {
			e.getWithExpr().accept(this);
		}
	}
	
	@Override
	public void visit_time_precision_stmt(SVDBTimePrecisionStmt s) {
		
	}
	
	@Override
	public void visit_time_units_stmt(SVDBTimeUnitsStmt s) {
		
	}
	
	@Override
	public void visit_type_expr(SVDBTypeExpr e) {
		if (e.getTypeInfo() != null) {
			e.getTypeInfo().accept(this);
		}
	}
	
	protected void visit_type_info(SVDBTypeInfo t) {
		for (SVDBVarDimItem d : t.getArrayDim()) {
			d.accept(this);
		}
	}
	
	@Override
	public void visit_type_info_builtin_net(SVDBTypeInfoBuiltinNet t) {
		do_accept(t.getTypeInfo());
		visit_type_info(t);
	}
	
	@Override
	public void visit_type_info_class_item(SVDBTypeInfoClassItem c) {
		visit_type_info(c);
		do_accept(c.getParamAssignList());
	}
	
	@Override
	public void visit_type_info_class_type(SVDBTypeInfoClassType c) {
		for (SVDBTypeInfoClassItem i : c.getTypeInfo()) {
			i.accept(this);
		}
		visit_type_info_class_item(c);
	}
	
	@Override
	public void visit_type_info_enum(SVDBTypeInfoEnum e) {
		visit_type_info(e);
		for (SVDBTypeInfoEnumerator en : e.getEnumerators()) {
			en.accept(this);
		}
	}
	
	@Override
	public void visit_type_info_enumerator(SVDBTypeInfoEnumerator e) {
		do_accept(e.getExpr());
		visit_type_info(e);
	}
	
	@Override
	public void visit_type_info_fwd_decl(SVDBTypeInfoFwdDecl f) {
		
	}
	
	@Override
	public void visit_type_info_module_ifc(SVDBTypeInfoModuleIfc t) {
		visit_type_info_user_def(t);
	}
	
	@Override
	public void visit_type_info_struct(SVDBTypeInfoStruct s) {
		for (SVDBVarDeclStmt f : s.getFields()) {
			f.accept(this);
		}
	}
	
	@Override
	public void visit_type_info_union(SVDBTypeInfoUnion u) {
		for (ISVDBItemBase f : u.getItems()) {
			f.accept(this);
		}
	}
	
	@Override
	public void visit_type_info_user_def(SVDBTypeInfoUserDef t) {
		do_accept(t.getParameters());
		for (ISVDBItemBase i : t.getItems()) {
			i.accept(this);
		}
	}
	
	@Override
	public void visit_typedef_stmt(SVDBTypedefStmt s) {
		do_accept(s.getTypeInfo());
	}
	
	@Override
	public void visit_unary_expr(SVDBUnaryExpr e) {
		if (e.getExpr() != null) {
			e.getExpr().accept(this);
		}
	}

	protected void visit_scope(ISVDBChildParent p) {
		for (ISVDBChildItem c : p.getChildren()) {
			c.accept(this);
		}
	}

	@Override
	public void visit_var_decl_item(SVDBVarDeclItem i) {
		do_accept(i.getInitExpr());
	}

	@Override
	public void visit_var_decl_stmt(SVDBVarDeclStmt s) {
		do_accept(s.getTypeInfo());
		
		visit_scope(s);
	}
	
	@Override
	public void visit_var_dim_item(SVDBVarDimItem i) {
		do_accept(i.getExpr(), i.getTypeInfo());
	}
	
	@Override
	public void visit_wait_fork_stmt(SVDBWaitForkStmt s) {
		visit_wait_stmt(s);
	}
	
	@Override
	public void visit_wait_order_stmt(SVDBWaitOrderStmt s) {
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_wait_stmt(SVDBWaitStmt s) {
		do_accept(s.getExpr());
		visit_body_stmt(s);
	}
	
	@Override
	public void visit_while_stmt(SVDBWhileStmt s) {
		do_accept(s.getExpr());
		visit_body_stmt(s);
	}
	
	private void do_accept(ISVDBItemBase i1) {
		if (i1 != null) {
			i1.accept(this);
		}
	}
	
	private void do_accept(
			ISVDBItemBase i1,
			ISVDBItemBase i2) {
		if (i1 != null) {
			i1.accept(this);
		}
		if (i2 != null) {
			i2.accept(this);
		}
	}
	
	private void do_accept(
			ISVDBItemBase i1,
			ISVDBItemBase i2,
			ISVDBItemBase i3) {
		if (i1 != null) {
			i1.accept(this);
		}
		if (i2 != null) {
			i2.accept(this);
		}
		if (i3 != null) {
			i3.accept(this);
		}
	}
}

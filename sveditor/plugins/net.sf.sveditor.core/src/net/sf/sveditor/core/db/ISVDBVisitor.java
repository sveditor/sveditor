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
import net.sf.sveditor.core.db.stmt.SVDBBreakStmt;
import net.sf.sveditor.core.db.stmt.SVDBCaseItem;
import net.sf.sveditor.core.db.stmt.SVDBCaseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigCellClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigDefaultClauseStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigDesignStmt;
import net.sf.sveditor.core.db.stmt.SVDBConfigInstClauseStmt;
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

public interface ISVDBVisitor {
	
	void visit_action_block_stmt(SVDBActionBlockStmt s);

	void visit_alias(SVDBAlias a);
	
	void visit_always_stmt(SVDBAlwaysStmt s);
	
	void visit_array_access_expr(SVDBArrayAccessExpr e);
	
	void visit_assert_stmt(SVDBAssertStmt s);
	
	void visit_assign(SVDBAssign a);
	
	void visit_assign_expr(SVDBAssignExpr e);
	
	void visit_assign_item(SVDBAssignItem a);
	
	void visit_assign_stmt(SVDBAssignStmt s);
	
	void visit_assignment_pattern_expr(SVDBAssignmentPatternExpr e);
	
	void visit_assignment_pattern_repeat_expr(SVDBAssignmentPatternRepeatExpr e);
	
	void visit_associative_array_assign_expr(SVDBAssociativeArrayAssignExpr e);
	
	void visit_associative_array_elem_assign_expr(SVDBAssociativeArrayElemAssignExpr e);
	
	void visit_assume_stmt(SVDBAssumeStmt s);
	
	void visit_binary_expr(SVDBBinaryExpr e);
	
	void visit_bind(SVDBBind b);
	
	void visit_block_stmt(SVDBBlockStmt s);
	
	void visit_break_stmt(SVDBBreakStmt s);
	
	
	void visit_case_item(SVDBCaseItem s);
	
	void visit_case_stmt(SVDBCaseStmt s);
	
	void visit_cast_expr(SVDBCastExpr e);
	
	void visit_class_decl(SVDBClassDecl c);

	void visit_clocked_property_expr(SVDBClockedPropertyExpr e);
	
	void visit_clocking_block(SVDBClockingBlock b);
	
	void visit_clocking_event_expr(SVDBClockingEventExpr e);
	
	void visit_concatenation_expr(SVDBConcatenationExpr e);
	
	void visit_cond_expr(SVDBCondExpr e);
	
	void visit_config_decl(SVDBConfigDecl c);
	
	void visit_config_cell_clause_stmt(SVDBConfigCellClauseStmt s);
	
	void visit_config_default_clause_stmt(SVDBConfigDefaultClauseStmt s);
	
	void visit_config_design_stmt(SVDBConfigDesignStmt s);
	
	void visit_config_inst_clause_stmt(SVDBConfigInstClauseStmt s);
	
	void visit_constraint(SVDBConstraint c);
	
	void visit_constraint_dist_list_item(SVDBConstraintDistListItem i);
	
	void visit_constraint_dist_list_stmt(SVDBConstraintDistListStmt s);
	
	void visit_constraint_foreach_stmt(SVDBConstraintForeachStmt s);
	
	void visit_constraint_if_stmt(SVDBConstraintIfStmt s);
	
	void visit_constraint_impl_stmt(SVDBConstraintImplStmt s);
	
	void visit_constraint_set_stmt(SVDBConstraintSetStmt s);
	
	void visit_constraint_solve_before_stmt(SVDBConstraintSolveBeforeStmt s);
	
	void visit_constraint_unique_stmt(SVDBConstraintUniqueStmt s);
	
	void visit_continue_stmt(SVDBContinueStmt s);
	
	void visit_cover_bins_expr(SVDBCoverBinsExpr e);
	
	void visit_cover_cross_bin_sel(SVDBCoverCrossBinsSel s);
	
	void visit_cover_stmt(SVDBCoverStmt s);
	
	void visit_coverage_cross_bins_select_stmt(SVDBCoverageCrossBinsSelectStmt s);
	
	void visit_coverage_option_stmt(SVDBCoverageOptionStmt s);
	
	void visit_covergroup(SVDBCovergroup c);
	
	void visit_coverpoint(SVDBCoverpoint c);
	
	void visit_coverpoint_bins(SVDBCoverpointBins b);
	
	void visit_coverpoint_cross(SVDBCoverpointCross c);
	
	void visit_coverpoint_expr(SVDBCoverpointExpr e);
	
	void visit_cross_bins_select_conditional_expr(SVDBCrossBinsSelectConditionExpr e);
	
	void visit_ctor_expr(SVDBCtorExpr e);
	
	void visit_cycle_delay_expr(SVDBCycleDelayExpr e);
	
	void visit_def_param_item(SVDBDefParamItem i);
	
	void visit_def_param_stmt(SVDBDefParamStmt s);
	
	void visit_delay_control_stmt(SVDBDelayControlStmt s);
	
	void visit_disable_fork_stmt(SVDBDisableForkStmt s);
	
	void visit_disable_stmt(SVDBDisableStmt s);
	
	void visit_do_while_stmt(SVDBDoWhileStmt s);
	
	void visit_doc_comment(SVDBDocComment c);
	
	void visit_event_control_stmt(SVDBEventControlStmt s);
	
	void visit_event_trigger_stmt(SVDBEventTriggerStmt s);
	
	void visit_export_item(SVDBExportItem i);
	
	void visit_export_stmt(SVDBExportStmt s);
	
	void visit_expr_stmt(SVDBExprStmt s);
	
	void visit_field_access_expr(SVDBFieldAccessExpr e);
	
	void visit_file(SVDBFile f);
	
	void visit_final_stmt(SVDBFinalStmt s);
	
	void visit_first_match_expr(SVDBFirstMatchExpr e);
	
	void visit_foreach_loopvar_expr(SVDBForeachLoopvarExpr e);
	
	void visit_foreach_stmt(SVDBForeachStmt s);
	
	void visit_forever_stmt(SVDBForeverStmt s);
	
	void visit_fork_stmt(SVDBForkStmt s);
	
	void visit_for_stmt(SVDBForStmt s);
	
	void visit_function_decl(SVDBFunction f);
	
	void visit_generate_block(SVDBGenerateBlock b);
	
	void visit_generate_for(SVDBGenerateFor g);
	
	void visit_generate_if(SVDBGenerateIf g);
	
	void visit_generate_region(SVDBGenerateRegion g);
	
	void visit_identifier_expr(SVDBIdentifierExpr e);
	
	void visit_if_stmt(SVDBIfStmt s);
	
	void visit_import_item(SVDBImportItem i);
	
	void visit_import_stmt(SVDBImportStmt s);
	
	void visit_inc_dec_expr(SVDBIncDecExpr e);
	
	void visit_include(SVDBInclude i);
	
	void visit_initial_stmt(SVDBInitialStmt s);
	
	void visit_inside_expr(SVDBInsideExpr e);
	
	void visit_interface_decl(SVDBInterfaceDecl i);

	void visit_labeled_stmt(SVDBLabeledStmt s);
	
	void visit_literal_expr(SVDBLiteralExpr e);
	
	void visit_macro_def(SVDBMacroDef d);
	
	void visit_macro_def_param(SVDBMacroDefParam d);
	
	void visit_marker(SVDBMarker m);
	
	void visit_mod_ifc_class_param(SVDBModIfcClassParam p);
	
	void visit_mod_ifc_decl(SVDBModIfcDecl d);
	
	void visit_mod_ifc_inst(SVDBModIfcInst i);
	
	void visit_mod_ifc_inst_item(SVDBModIfcInstItem i);
	
	void visit_modport_clocking_port_decl(SVDBModportClockingPortDecl p);
	
	void visit_modport_decl(SVDBModportDecl p);
	
	void visit_modport_item(SVDBModportItem i);
	
	void visit_modport_simple_port(SVDBModportSimplePort p);
	
	void visit_modport_simple_ports_decl(SVDBModportSimplePortsDecl p);
	
	void visit_modport_tf_port(SVDBModportTFPort p);
	
	void visit_modport_tf_ports_decl(SVDBModportTFPortsDecl d);
	
	void visit_module_decl(SVDBModuleDecl d);

	void visit_min_typ_max_expr(SVDBMinTypMaxExpr e);
	
	void visit_named_arg_expr(SVDBNamedArgExpr e);
	
	void visit_name_mapped_expr(SVDBNameMappedExpr e);
	
	void visit_null_expr(SVDBNullExpr e);
	
	void visit_null_stmt(SVDBNullStmt s);
	
	void visit_open_range_list_expr(SVDBOpenRangeListExpr e);
	
	void visit_package_decl(SVDBPackageDecl p);
	
	void visit_param_id_expr(SVDBParamIdExpr e);
	
	void visit_param_port_decl(SVDBParamPortDecl d);
	
	void visit_param_value_assign(SVDBParamValueAssign a);
	
	void visit_param_value_assign_list(SVDBParamValueAssignList l);
	
	void visit_procedural_cont_assign_stmt(SVDBProceduralContAssignStmt s);
	
	void visit_program_decl(SVDBProgramDecl p);
	
	void visit_property(SVDBProperty p);
	
	void visit_property_case_item(SVDBPropertyCaseItem i);
	
	void visit_property_case_stmt(SVDBPropertyCaseStmt s);
	
	void visit_property_if_stmt(SVDBPropertyIfStmt s);
	
	void visit_property_spec_expr(SVDBPropertySpecExpr e);
	
	void visit_property_weak_strong_expr(SVDBPropertyWeakStrongExpr e);
	
	void visit_randomize_call_expr(SVDBRandomizeCallExpr e);
	
	void visit_randseq_stmt(SVDBRandseqStmt s);
	
	void visit_randseq_prod_stmt(SVDBRandseqProdStmt s);
	
	void visit_range_dollar_bound_expr(SVDBRangeDollarBoundExpr e);
	
	void visit_range_expr(SVDBRangeExpr e);
	
	void visit_ref_elem_expr(SVDBRefElemExpr e);
	
	void visit_ref_path_expr(SVDBRefPathExpr e);
	
	void visit_repeat_stmt(SVDBRepeatStmt s);
	
	void visit_return_stmt(SVDBReturnStmt s);
	
	void visit_sequence(SVDBSequence s);
	
	void visit_sequence_clocking_expr(SVDBSequenceClockingExpr e);
	
	void visit_sequence_cycle_delay_expr(SVDBSequenceCycleDelayExpr e);
	
	void visit_sequence_dist_expr(SVDBSequenceDistExpr e);
	
	void visit_sequence_match_item_expr(SVDBSequenceMatchItemExpr e);
	
	void visit_sequence_repetition_expr(SVDBSequenceRepetitionExpr e);
	
	void visit_string_expr(SVDBStringExpr e);
	
	void visit_task(SVDBTask t);
	
	void visit_tf_call_expr(SVDBTFCallExpr e);
	
	void visit_tf_param_list(SVDBTFParamList p);
	
	void visit_time_precision_stmt(SVDBTimePrecisionStmt s);
	
	void visit_time_units_stmt(SVDBTimeUnitsStmt s);
	
	void visit_type_expr(SVDBTypeExpr e);
	
	void visit_type_info_builtin(SVDBTypeInfoBuiltin t);
	
	void visit_type_info_builtin_net(SVDBTypeInfoBuiltinNet t);
	
	void visit_type_info_class_item(SVDBTypeInfoClassItem c);
	
	void visit_type_info_class_type(SVDBTypeInfoClassType c);
	
	void visit_type_info_enum(SVDBTypeInfoEnum e);
	
	void visit_type_info_enumerator(SVDBTypeInfoEnumerator e);
	
	void visit_type_info_fwd_decl(SVDBTypeInfoFwdDecl f);
	
	void visit_type_info_module_ifc(SVDBTypeInfoModuleIfc t);
	
	void visit_type_info_struct(SVDBTypeInfoStruct s);
	
	void visit_type_info_union(SVDBTypeInfoUnion u);
	
	void visit_type_info_user_def(SVDBTypeInfoUserDef t);
	
	void visit_typedef_stmt(SVDBTypedefStmt s);
	
	void visit_unary_expr(SVDBUnaryExpr e);
	
	void visit_var_decl_item(SVDBVarDeclItem i);
	
	void visit_var_decl_stmt(SVDBVarDeclStmt s);
	
	void visit_var_dim_item(SVDBVarDimItem i);
	
	void visit_wait_fork_stmt(SVDBWaitForkStmt s);
	
	void visit_wait_order_stmt(SVDBWaitOrderStmt s);

	void visit_wait_stmt(SVDBWaitStmt s);
	
	void visit_while_stmt(SVDBWhileStmt s);
	

}

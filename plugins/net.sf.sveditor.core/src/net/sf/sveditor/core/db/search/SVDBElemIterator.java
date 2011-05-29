package net.sf.sveditor.core.db.search;

import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBClockingBlock;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCoverCrossBinsSel;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBCoverpoint;
import net.sf.sveditor.core.db.SVDBCoverpointBins;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
import net.sf.sveditor.core.db.SVDBGenerateFor;
import net.sf.sveditor.core.db.SVDBGenerateIf;
import net.sf.sveditor.core.db.SVDBGenerateRegion;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBModportClockingPortDecl;
import net.sf.sveditor.core.db.SVDBModportDecl;
import net.sf.sveditor.core.db.SVDBModportItem;
import net.sf.sveditor.core.db.SVDBModportPortsDecl;
import net.sf.sveditor.core.db.SVDBModportSimplePort;
import net.sf.sveditor.core.db.SVDBModportSimplePortsDecl;
import net.sf.sveditor.core.db.SVDBModportTFPort;
import net.sf.sveditor.core.db.SVDBModportTFPortsDecl;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBPreProcCond;
import net.sf.sveditor.core.db.SVDBProgramDecl;
import net.sf.sveditor.core.db.SVDBProperty;
import net.sf.sveditor.core.db.SVDBSequence;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltinNet;
import net.sf.sveditor.core.db.SVDBTypeInfoClassItem;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoFwdDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoModuleIfc;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.stmt.SVDBActionBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssertStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssignStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssumeStmt;
import net.sf.sveditor.core.db.stmt.SVDBBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBLabeledStmt;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public class SVDBElemIterator {
	private Stack<ISVDBItemBase>			fStack;
	
	public SVDBElemIterator() {
		fStack  = new Stack<ISVDBItemBase>();
	}
	
	public void visit(ISVDBItemBase item) {
		fStack.clear();
		visit_int(item);
	}
	
	protected void visit_int(ISVDBItemBase item) {
		switch (item.getType()) {
			case File:
				file((SVDBFile)item);
				break;
			case ModuleDecl:
				module_decl((SVDBModIfcDecl)item);
				break;
			case ClassDecl:
				class_decl((SVDBClassDecl)item);
				break;
			case InterfaceDecl:
				interface_decl((SVDBModIfcDecl)item);
				break;
			case ProgramDecl:
				program_decl((SVDBProgramDecl)item);
				break;
			case Task:
			case Function:
				tf_decl((SVDBTask)item);
				break;
			case ModIfcInst:
				mod_ifc_inst((SVDBModIfcInst)item);
				break;
			case ModIfcInstItem:
				mod_ifc_inst_item((SVDBModIfcInstItem)item);
				break;
			case ModportDecl:
				modport_decl((SVDBModportDecl)item);
				break;
			case ModportItem:
				modport_item((SVDBModportItem)item);
				break;
			case ModportSimplePortsDecl:
				modport_simple_ports_decl((SVDBModportSimplePortsDecl)item);
				break;
			case ModportSimplePort:
				modport_simple_port((SVDBModportSimplePort)item);
				break;
			case ModportClockingPortDecl:
				modport_clocking_port_decl((SVDBModportClockingPortDecl)item);
				break;
			case ModportTFPortsDecl:
				modport_tf_ports_decl((SVDBModportTFPortsDecl)item);
				break;
			case ModportTFPort:
				modport_tf_port((SVDBModportTFPort)item);
				break;
			case MacroDef:
				macro_def((SVDBMacroDef)item);
				break;
			case PreProcCond:
				pre_proc_cond((SVDBPreProcCond)item);
				break;
			case Include:
				include((SVDBInclude)item);
				break;
			case PackageDecl:
				package_decl((SVDBPackageDecl)item);
				break;
			case Covergroup:
				covergroup((SVDBCovergroup)item);
				break;
			case Coverpoint:
				coverpoint((SVDBCoverpoint)item);
				break;
			case CoverpointBins:
				coverpoint_bins((SVDBCoverpointBins)item);
				break;
			case CoverpointCross:
				coverpoint_cross((SVDBCoverpointCross)item);
				break;
			case CoverCrossBinsSel:
				cover_cross_bins_sel((SVDBCoverCrossBinsSel)item);
				break;
			case Sequence:
				sequence((SVDBSequence)item);
				break;
			case Property:
				property((SVDBProperty)item);
				break;
			case ModIfcClassParam:
				mod_ifc_class_param((SVDBModIfcClassParam)item);
				break;
			case Constraint:
				constraint((SVDBConstraint)item);
				break;
			case Assign:
				assign((SVDBAssign)item);
				break;
			case Marker:
				marker((SVDBMarker)item);
				break;
			case ParamValueAssign:
				param_value_assign((SVDBParamValueAssign)item);
				break;
			case ParamValueAssignList:
				param_value_assign_list((SVDBParamValueAssignList)item);
				break;
			case GenerateBlock:
				generate_block((SVDBGenerateBlock)item);
				break;
			case GenerateFor:
				generate_for((SVDBGenerateFor)item);
				break;
			case GenerateIf:
				generate_if((SVDBGenerateIf)item);
				break;
			case GenerateRegion:
				generate_region((SVDBGenerateRegion)item);
				break;
			case ClockingBlock:
				clocking_block((SVDBClockingBlock)item);
				break;
		
		// Data Types
			case TypeInfoBuiltin:
				type_info_builtin((SVDBTypeInfoBuiltin)item);
				break;
			case TypeInfoBuiltinNet:
				type_info_builtin_net((SVDBTypeInfoBuiltinNet)item);
				break;
			case TypeInfoClassItem:
				type_info_class_item((SVDBTypeInfoClassItem)item);
				break;
			case TypeInfoClassType:
				type_info_class_type((SVDBTypeInfoClassType)item);
				break;
			case TypeInfoEnum:
				type_info_enum((SVDBTypeInfoEnum)item);
				break;
			case TypeInfoFwdDecl:
				type_info_fwd_decl((SVDBTypeInfoFwdDecl)item);
				break;
			case TypeInfoStruct:
				type_info_struct((SVDBTypeInfoStruct)item);
				break;
			case TypeInfoUserDef:
				type_info_user_def((SVDBTypeInfoUserDef)item);
				break;
			case TypeInfoModuleIfc:
				type_info_module_ifc((SVDBTypeInfoModuleIfc)item);
				break;

		// Statement items
			case ActionBlockStmt:
				action_block_stmt((SVDBActionBlockStmt)item);
				break;
			case AlwaysStmt:
				always_stmt((SVDBAlwaysStmt)item);
				break;
			case AssertStmt:
				assert_stmt((SVDBAssertStmt)item);
				break;
			case AssignStmt:
				assign_stmt((SVDBAssignStmt)item);
				break;
			case AssumeStmt:
				assume_stmt((SVDBAssumeStmt)item);
				break;
			case LabeledStmt:
				labeled_stmt((SVDBLabeledStmt)item);
				break;
			case BlockStmt:
				block_stmt((SVDBBlockStmt)item);
				break;
/** TODO:				
			case ConstraintDistListStmt:
				constraint_dist_list_stmt((SVDBConstraintDistListStmt)item);
				break;
			case ConstraintDistListItem:
				constraint_dist_list_item((SVDBConstraintDistListItem)item);
				break;
			case ConstraintForeachStmt:
				constraint_foreach_stmt((SVDBConstraintForeachStmt)item);
				break;
			case ConstraintIfStmt:
				constraint_if_stmt((SVDBConstraintIfStmt)item);
				break;
			case ConstraintImplStmt:
				constraint_impl_stmt((SVDBConstraintImplStmt)item);
				break;
			case ConstraintSetStmt:
				constraint_set_stmt((SVDBConstraintSetStmt)item);
				break;
			case ConstraintSolveBeforeStmt:
				constraint_solve_before_stmt((SVDBConstraintSolveBeforeStmt)item);
				break;
			case DisableStmt:
				disable_stmt((SVDBDisableStmt)item);
				break;
			case DisableForkStmt:
				disable_fork_stmt((SVDBDisableForkStmt)item);
				break;
			case DefParamStmt:
				def_param_stmt((SVDBDefParamStmt)item);
				break;
			case DefParamItem:
				def_param_item((SVDBDefParamItem)item);
				break;
			case DelayControlStmt:
				delay_control_stmt((SVDBDelayControlStmt)item);
				break;
			case DoWhileStmt:
				do_while_stmt((SVDBDoWhileStmt)item);
				break;
			case EventControlStmt:
				event_control_stmt((SVDBEventControlStmt)item);
				break;
			case ExportStmt:
				export_stmt((SVDBExportStmt)item);
				break;
			case ExprStmt:
				expr_stmt((SVDBExprStmt)item);
				break;
			case FinalStmt:
				final_stmt((SVDBFinalStmt)item);
				break;
			case ForStmt:
				for_stmt((SVDBForStmt)item);
				break;
			case ForeachStmt:
				foreach_stmt((SVDBForeachStmt)item);
				break;
			case ForeverStmt:
				forever_stmt((SVDBForeverStmt)item);
				break;
			case NullStmt:
				null_stmt((SVDBNullStmt)item);
				break;
			case ProceduralContAssignStmt:
				proecedural_cont_assign_stmt((SVDBProceduralContAssignStmt)item);
				break;
			case WhileStmt:
				while_stmt((SVDBWhileStmt)item);
				break;
			case RepeatStmt:
				repeat_stmt((SVDBRepeatStmt)item);
				break;
			case IfStmt:
				if_stmt((SVDBIfStmt)item);
				break;
			case ImportStmt:
				import_stmt((SVDBImportStmt)item);
				break;
			case InitialStmt:
				initial_stmt((SVDBInitialStmt)item);
				break;
			case ForkStmt:
				fork_stmt((SVDBForkStmt)item);
				break;
			case CaseStmt:
				case_stmt((SVDBCaseStmt)item);
				break;
			case CaseItem:
				case_item((SVDBCaseItem)item);
				break;
			case WaitStmt:
				wait_stmt((SVDBWaitStmt)item);
				break;
			case WaitForkStmt:
				wait_fork_stmt((SVDBWaitForkStmt)item);
				break;
			case WaitOrderStmt:
				wait_order_stmt((SVDBWaitOrderStmt)item);
				break;
			case ReturnStmt:
				return_stmt((SVDBReturnStmt)item);
				break;
			case BreakStmt:
				break_stmt((SVDBBreakStmt)item);
				break;
			case ContinueStmt:
				continue_stmt((SVDBContinueStmt)item);
				break;
			case EventTriggerStmt:
				event_trigger_stmt((SVDBEventTriggerStmt)item);
				break;
			 */
		
			case VarDeclStmt:
				var_decl_stmt((SVDBVarDeclStmt)item);
				break;
			case VarDeclItem:
				var_decl_item((SVDBVarDeclItem)item);
				break;
			 /*
			case VarDimItem:
				var_dim_item((SVDBVarDimItem)item);
				break;
			case ParamPortDecl:
				param_port_decl((SVDBParamPortDecl)item);
				break;
		
			case TypedefStmt:
				typedef_stmt((SVDBTypedefStmt)item);
				break;
		
			case CoverageOptionStmt:
				coverage_option_stmt((SVDBCoverageOptionStmt)item);
				break;
			case CoverageCrossBinsSelectStmt:
				coverage_cross_bins_select_stmt((SVDBCoverageCrossBinsSelectStmt)item);
				break;

			// Expressions
			case ArrayAccessExpr:
				array_access_expr((SVDBArrayAccessExpr)item);
				break;
			case AssignExpr:
				assign_expr((SVDBAssignExpr)item);
				break;
			case AssignmentPatternExpr:
				assignment_pattern_expr((SVDBAssignmentPatternExpr)item);
				break;
			case AssignmentPatternRepeatExpr:
				assignment_pattern_repeat_expr((SVDBAssignmentPatternRepeatExpr)item);
				break;
			case BinaryExpr:
				binary_expr((SVDBBinaryExpr)item);
				break;
			case CastExpr:
				cast_expr((SVDBCastExpr)item);
				break;
			case ClockingEventExpr:
				clocking_event_expr((SVDBClockingEventExpr)item);
				break;
			case ConcatenationExpr:
				concatenation_expr((SVDBConcatenationExpr)item);
				break;
			case CondExpr:
				cond_expr((SVDBCondExpr)item);
				break;
			case CrossBinsSelectConditionExpr:
				cross_bins_select_condition_expr((SVDBCrossBinsSelectConditionExpr)item);
				break;
			case CtorExpr:
				ctor_expr((SVDBCtorExpr)item);
				break;
			case FieldAccessExpr:
				field_access_expr((SVDBFieldAccessExpr)item);
				break;
			case IdentifierExpr:
				identifier_expr((SVDBIdentifierExpr)item);
				break;
			case IncDecExpr:
				inc_dec_expr((SVDBIncDecExpr)item);
				break;
			case InsideExpr:
				inside_expr((SVDBInsideExpr)item);
				break;
			case LiteralExpr:
				literal_expr((SVDBLiteralExpr)item);
				break;
			case NamedArgExpr: // .ARG(value)
				named_arg_expr((SVDBNamedArgExpr)item);
				break;
			case NullExpr:
				null_expr((SVDBNullExpr)item);
				break;
			case ParenExpr:
				paren_expr((SVDBParenExpr)item);
				break;
			case RandomizeCallExpr:
				randomize_call_expr((SVDBRandomizeCallExpr)item);
				break;
			case RangeDollarBoundExpr:
				range_dollar_bound_expr((SVDBRangeDollarBoundExpr)item);
				break;
			case RangeExpr:
				range_expr((SVDBRangeExpr)item);
				break;
			case TFCallExpr:
				tf_call_expr((SVDBTFCallExpr)item);
				break;
			case UnaryExpr:
				unary_expr((SVDBUnaryExpr)item);
				break;
		
			case StringExpr:
				string_expr((SVDBStringExpr)item);
				break; 
 */				
		
//		CoverpointExpr,
//		CoverBinsExpr,
		
		}
		
	}

	protected void file(SVDBFile file) {
		fStack.push(file);
		for (ISVDBChildItem item : file.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void module_decl(SVDBModIfcDecl module) {
		fStack.push(module);
		for (ISVDBChildItem item : module.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}

	protected void class_decl(SVDBClassDecl cls) {
		fStack.push(cls);
		for (ISVDBChildItem item : cls.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void interface_decl(SVDBModIfcDecl ifc) {
		fStack.push(ifc);
		for (ISVDBChildItem item : ifc.getChildren()){
			visit(item);
		}
		
		fStack.pop();
	}

	protected void program_decl(SVDBProgramDecl prog) {
		fStack.push(prog);
		for (ISVDBChildItem item : prog.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	protected void tf_decl(SVDBTask tf) {
		fStack.push(tf);
		if (tf.getType() == SVDBItemType.Function) {
			visit(((SVDBFunction)tf).getReturnType());
		}
		tf_param_port_list(tf.getParams());
		
		fStack.pop();
	}
	
	protected void tf_param_port_list(List<SVDBParamPortDecl> ports) {
		for (SVDBParamPortDecl p : ports) {
			visit(p);
		}
	}
	
	protected void mod_ifc_inst(SVDBModIfcInst inst) {
		fStack.push(inst);
		for (ISVDBChildItem item : inst.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void mod_ifc_inst_item(SVDBModIfcInstItem item) {
		fStack.push(item);
		// TODO: decl_name (?)
		visit(item.getPortMap());
		fStack.pop();
	}
	
	protected void modport_decl(SVDBModportDecl decl) {
		fStack.push(decl);
		for (ISVDBChildItem pi : decl.getChildren()) {
			visit(pi);
		}
		fStack.pop();
	}
	
	protected void modport_item(SVDBModportItem item) {
		for (SVDBModportPortsDecl p : item.getPortsList()) {
			visit(p);
		}
	}
	
	protected void modport_simple_ports_decl(SVDBModportSimplePortsDecl decl) {
		fStack.push(decl);
		for (SVDBModportSimplePort p : decl.getPortList()) {
			visit(p);
		}
		fStack.pop();
	}
	
	protected void modport_simple_port(SVDBModportSimplePort port) {
		fStack.push(port);
		// TODO: port.getPortId()
		visit(port.getExpr());
		fStack.pop();
	}
	
	protected void modport_clocking_port_decl(SVDBModportClockingPortDecl port) {
		// TODO: port.getPortId()
	}
	
	protected void modport_tf_ports_decl(SVDBModportTFPortsDecl port) {
		for (ISVDBChildItem p : port.getPorts()) {
			visit(p);
		}
	}
	
	protected void modport_tf_port(SVDBModportTFPort port) {
		// TODO: port.getPortId()
	}
	
	protected void macro_def(SVDBMacroDef macro) {
		// TODO: name
	}
	
	protected void pre_proc_cond(SVDBPreProcCond cond) {
		fStack.push(cond);
		for (ISVDBChildItem item : cond.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void include(SVDBInclude inc) {
		
	}
	
	protected void package_decl(SVDBPackageDecl pkg) {
		fStack.push(pkg);
		for (ISVDBChildItem item : pkg.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void covergroup(SVDBCovergroup cg) {
		fStack.push(cg);
		for (ISVDBChildItem item : cg.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void coverpoint(SVDBCoverpoint cp) {
		fStack.push(cp);
		if (cp.getIFF() != null) {
			visit(cp.getIFF());
		}
		for (ISVDBChildItem item : cp.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void coverpoint_bins(SVDBCoverpointBins bins) {
		// TODO:
	}
	
	protected void coverpoint_cross(SVDBCoverpointCross cross) {
		fStack.push(cross);
		// TODO: name, references (?)
		for (ISVDBChildItem item : cross.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void cover_cross_bins_sel(SVDBCoverCrossBinsSel sel) {
		// TODO:
	}
	
	protected void sequence(SVDBSequence seq) {
		fStack.push(seq);
		for (ISVDBChildItem item : seq.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void property(SVDBProperty prop) {
		fStack.push(prop);
		for (ISVDBChildItem item : prop.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void mod_ifc_class_param(SVDBModIfcClassParam param) {
		fStack.push(param);
		// TODO: param.getName();
		visit(param.getDefault());
		fStack.pop();
	}
	
	protected void constraint(SVDBConstraint c) {
		fStack.push(c);
		// TODO: name
		for (ISVDBChildItem item : c.getChildren()) {
			visit(item);
		}
		fStack.pop();
	}
	
	protected void assign(SVDBAssign assign) {
		fStack.push(assign);
		visit(assign.getLHS());
		visit(assign.getRHS());
		fStack.pop();
	}
	
	protected void marker(SVDBMarker marker) {
		// TODO:
	}
	
	protected void param_value_assign(SVDBParamValueAssign assign) {
		// TODO: assign.getName();
		visit(assign.getValue());
	}
	
	protected void param_value_assign_list(SVDBParamValueAssignList assign_list) {
		fStack.push(assign_list);
		for (SVDBParamValueAssign a : assign_list.getParameters()) {
			visit(a);
		}
		fStack.pop();
	}
	
	protected void generate_block(SVDBGenerateBlock block) {
		fStack.push(block);
		for (ISVDBChildItem c : block.getChildren()) {
			visit(c);
		}
		fStack.pop();
	}
	
	protected void generate_for(SVDBGenerateFor gen_for) {
		// TODO:
	}
	
	protected void generate_if(SVDBGenerateIf gen_if) {
		// TODO:
	}
	
	protected void generate_region(SVDBGenerateRegion region) {
		// TODO:
	}
	
	protected void clocking_block(SVDBClockingBlock block) {
		// TODO:
	}
	
	protected void type_info_builtin(SVDBTypeInfoBuiltin type) {
		// TODO:
	}
	
	protected void type_info_builtin_net(SVDBTypeInfoBuiltinNet type) {
		// TODO:
	}
	
	protected void type_info_class_type(SVDBTypeInfoClassType type) {
		// TODO:
	}
	
	protected void type_info_class_item(SVDBTypeInfoClassItem type_item) {
		// TODO:
	}
	
	protected void type_info_enum(SVDBTypeInfoEnum type) {
		// TODO:
	}
	
	protected void type_info_fwd_decl(SVDBTypeInfoFwdDecl type) {
		// TODO:
	}
	
	protected void type_info_struct(SVDBTypeInfoStruct type) {
		// TODO:
	}
	
	protected void type_info_module_ifc(SVDBTypeInfoModuleIfc type) {
		// TODO:
	}
	protected void type_info_user_def(SVDBTypeInfoUserDef type) {
		// TODO:
	}
	
	protected void action_block_stmt(SVDBActionBlockStmt stmt) {
		fStack.push(stmt);
		// TODO:
		fStack.pop();
	}
	
	protected void always_stmt(SVDBAlwaysStmt stmt) {
		fStack.push(stmt);
		// TODO: event ?
		visit(stmt.getBody());
		fStack.pop();
	}
	
	protected void assert_stmt(SVDBAssertStmt stmt) {
		fStack.push(stmt);
		// TODO:
		// stmt.getActionBlock()
		fStack.pop();
	}
	
	protected void assign_stmt(SVDBAssignStmt stmt) {
		fStack.push(stmt);
		visit(stmt.getLHS());
		visit(stmt.getRHS());
		fStack.pop();
	}
	
	protected void assume_stmt(SVDBAssumeStmt stmt) {
		// TODO:
	}
	
	protected void labeled_stmt(SVDBLabeledStmt stmt) {
		visit(stmt.getBody());
	}
	
	protected void block_stmt(SVDBBlockStmt block) {
		fStack.push(block);
		for (ISVDBChildItem c : block.getChildren()) {
			visit(c);
		}
		fStack.pop();
	}

	protected void var_decl_stmt(SVDBVarDeclStmt stmt) {
		visit(stmt.getTypeInfo());
		
		for (ISVDBChildItem c : stmt.getChildren()) {
			visit(c);
		}
	}
	
	protected void var_decl_item(SVDBVarDeclItem item) {
		if (item.getInitExpr() != null) {
			visit(item.getInitExpr());
		}
	}
	
}

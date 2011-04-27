package net.sf.sveditor.core.expr_utils;

import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBCastExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVDBParenExpr;
import net.sf.sveditor.core.db.expr.SVDBTFCallExpr;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameInClassHierarchy;
import net.sf.sveditor.core.db.search.SVDBFindByNameInScopes;
import net.sf.sveditor.core.db.search.SVDBFindNamedClass;
import net.sf.sveditor.core.db.search.SVDBFindParameterizedClass;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVContentAssistExprVisitor {
	private LogHandle					fLog;
	private ISVDBIndexIterator			fIndexIt;
	private ISVDBScopeItem				fScope;
	private SVDBClassDecl				fClassScope;
	private ISVDBFindNameMatcher		fNameMatcher;
	private Stack<ISVDBItemBase>		fResolveStack;
	private SVDBFindNamedClass 			fFindNamedClass;
	private SVDBFindParameterizedClass	fFindParameterizedClass;
	
	private class SVAbortException extends RuntimeException {
		private static final long serialVersionUID = 1L;

		/*
		public SVAbortException() {
			super();
		}
		 */
		
		public SVAbortException(String msg) {
			super(msg);
		}
	}
	
	public SVContentAssistExprVisitor(
			ISVDBScopeItem			scope,
			ISVDBFindNameMatcher	name_matcher,
			ISVDBIndexIterator 		index_it) {
		fLog = LogFactory.getLogHandle("SVContentAssistExprVisitor");
		fResolveStack = new Stack<ISVDBItemBase>();
		fScope = scope;
		fNameMatcher = name_matcher;
		fIndexIt = index_it;
		fFindNamedClass = new SVDBFindNamedClass(fIndexIt);
		fFindParameterizedClass = new SVDBFindParameterizedClass(fIndexIt);
		classifyScope();
	}
	
	private void classifyScope() {
		ISVDBChildItem parent = fScope;
		
		fClassScope = null;
		
		if (fScope == null) {
			return;
		}
		
		while (parent != null && parent.getType() != SVDBItemType.ClassDecl) {
			parent = parent.getParent();
		}
		
		if (parent != null && parent.getType() == SVDBItemType.ClassDecl) {
			fClassScope = (SVDBClassDecl)parent;
		} else {
			// See if this scope is an external task/function
			if (fScope.getType() == SVDBItemType.Function || 
					fScope.getType() == SVDBItemType.Task) {
				String name = ((SVDBTask)fScope).getName();
				int idx;
				if ((idx = name.indexOf("::")) != -1) {
					String class_name = name.substring(0, idx);
					System.out.println("class_name: " + class_name);
					List<SVDBClassDecl> result = fFindNamedClass.find(class_name);
					
					if (result.size() > 0) {
						fClassScope = result.get(0);
					}
				}
			}
		}
	}
	
	public ISVDBItemBase findItem(SVDBExpr expr) {
		fLog.debug("findItem");
		fResolveStack.clear();
		
		try {
			visit(expr);
			if (fResolveStack.size() > 0) {
				return fResolveStack.pop();
			}
		} catch (SVAbortException e) {
			e.printStackTrace();
		}

		return null;
	}

	public ISVDBItemBase findTypeItem(SVDBExpr expr) {
		fLog.debug("findItemType");
		fResolveStack.clear();
		
		try {
			visit(expr);
			if (fResolveStack.size() > 0) {
				return findType(fResolveStack.pop());
			}
		} catch (SVAbortException e) {
			e.printStackTrace();
		}

		return null;
	}

	protected void visit(SVDBExpr expr) {
		switch (expr.getType()) {
				
			case CastExpr:
				cast_expr((SVDBCastExpr)expr);
				break;
				
			case FieldAccessExpr:
				field_access_expr((SVDBFieldAccessExpr)expr);
				break;
				
			case IdentifierExpr:
				identifier_expr((SVDBIdentifierExpr)expr);
				break;
				
			case TFCallExpr:
				tf_call((SVDBTFCallExpr)expr);
				break;

			case ParenExpr:
				visit(((SVDBParenExpr)expr).getExpr());
				break;

			case AssignExpr:
				assign_expr((SVDBAssignExpr)expr);
				break;

			case ClockingEventExpr:
			case ConcatenationExpr:
			case CondExpr:
			case CrossBinsSelectConditionExpr:
			case CtorExpr:
			case ArrayAccessExpr:
			case AssignmentPatternExpr:
			case AssignmentPatternRepeatExpr:
			case BinaryExpr:
			case RandomizeCallExpr:
			case RangeDollarBoundExpr:
			case RangeExpr:
			case UnaryExpr:
			case IncDecExpr:
			case InsideExpr:
			case LiteralExpr:
			case NamedArgExpr: // .ARG(value)
			case NullExpr:
				throw new SVAbortException("Unsupport expression element: " + expr.getType());
				
			default:
				throw new SVAbortException("Unhandled expression element: " + expr.getType());
		}
	}
	
	protected void cast_expr(SVDBCastExpr expr) {
		fLog.debug("cast_expr: " + expr.getCastType().toString());
		
	}

	protected void field_access_expr(SVDBFieldAccessExpr expr) {
		fLog.debug("field_access_expr: (" + (expr.isStaticRef()?"::":".") + ")");
		visit(expr.getExpr());
		visit(expr.getLeaf());
	}
	
	private ISVDBItemBase findInScopeHierarchy(String name) {
		SVDBFindByNameInScopes finder = new SVDBFindByNameInScopes(fIndexIt);
		
		List<ISVDBItemBase> items = finder.find(fScope, name, true); 
		
		if (items.size() > 0) {
			return items.get(0);
		} else {
			return null;
		}
	}
	
	private ISVDBItemBase findInClassHierarchy(ISVDBChildItem root, String name) {
		SVDBFindByNameInClassHierarchy finder_h = 
			new SVDBFindByNameInClassHierarchy(fIndexIt, fNameMatcher);
		List<ISVDBItemBase> items = finder_h.find(root, name);
		
		if (items.size() > 0) {
			return items.get(0);
		} else {
			return null;
		}
	}
	
	/**
	 * Returns the type of the specified element.  
	 * @param item
	 * @return
	 */
	private ISVDBItemBase findType(ISVDBItemBase item) {
		SVDBTypeInfo   type = null;
		SVDBVarDimItem var_dim = null;
		fLog.debug("findType: " + SVDBItem.getName(item));
		
		if (item.getType() == SVDBItemType.VarDeclItem) {
			SVDBVarDeclItem var  = (SVDBVarDeclItem)item;
			SVDBVarDeclStmt stmt = var.getParent();
			
			var_dim = var.getArrayDim();
			type = stmt.getTypeInfo();
		} else if (item.getType() == SVDBItemType.ClassDecl) {
			// NULL transform: item is already a type
			fLog.debug("    item " + SVDBItem.getName(item) + " already a class");
			return item;
		}
		
		if (type != null) {
			if (type.getType() == SVDBItemType.TypeInfoUserDef) {
				SVDBFindByName finder_n = new SVDBFindByName(fIndexIt);

				List<ISVDBItemBase> item_l = finder_n.find(type.getName());
				
				if (item_l.size() > 0) {
					item = item_l.get(0);
				}
			}
			
			if (var_dim != null) {
				// TODO: should probably handle non-user base types
				if (item != null) {
					item = resolveArrayType(item, SVDBItem.getName(item), var_dim);
				}
			}
		}
		return item;
	}
	
	private ISVDBItemBase resolveArrayType(ISVDBItemBase base, String base_type, SVDBVarDimItem var_dim) {
		ISVDBItemBase ret = null;
		SVDBTypeInfoUserDef target_type_info = null;
		SVDBParamValueAssignList param_l = new SVDBParamValueAssignList();
		
		System.out.println("resolveArrayType: " + base + " " + base_type);
		
		switch (var_dim.getDimType()) {
			case Associative:
				target_type_info = new SVDBTypeInfoUserDef("__sv_builtin_assoc_array");
				param_l.addParameter("T", base_type);
				param_l.addParameter("IDX", var_dim.getExpr().toString());
				break;
			case Queue:
				target_type_info = new SVDBTypeInfoUserDef("__sv_builtin_queue");
				param_l.addParameter("T", base_type);
				break;
			case Sized:
			case Unsized:
				target_type_info = new SVDBTypeInfoUserDef("__sv_builtin_array");
				param_l.addParameter("T", base_type);
				break;
		}
		
		target_type_info.setParameters(param_l);
		
		// Locate the class
		if (target_type_info != null) {
			ret = fFindParameterizedClass.find(target_type_info);
		}
		
		return ret;
	}
	
	private ISVDBItemBase findRoot(String id) {
		ISVDBItemBase ret = null;
		List<ISVDBItemBase> r_l;

		fLog.debug("findRoot: " + id);

		if (id.equals("this") || id.equals("super")) {
			if (fClassScope != null) {
				if (id.equals("this")) {
					return fClassScope;
				} else {
					SVDBFindSuperClass finder = new SVDBFindSuperClass(fIndexIt);
					return finder.find(fClassScope);
				}
			}
		}
		
		// Check up the scopes in this class
		if ((ret = findInScopeHierarchy(id)) != null) {
			return ret;
		}
		
		// Check the super-class hierarchy
		if (fClassScope != null && (ret = findInClassHierarchy(fClassScope, id)) != null) {
			return ret;
		}

//		r_l = f
		
		return ret;
	}
	
	protected void identifier_expr(SVDBIdentifierExpr expr) {
		fLog.debug("identifier_expr: " + expr.getId());
		if (fResolveStack.size() == 0) {
			ISVDBItemBase item = findRoot(expr.getId());
			if (item == null) {
				String msg = "Failed to find root \"" + expr.getId() + "\"";
				fLog.debug(msg);
				throw new SVAbortException(msg);
			}
			fResolveStack.push(item);
		} else {
			fLog.debug("Resolve : " + expr.getId() + " relative to " + fResolveStack.peek());
			ISVDBItemBase item = findType(fResolveStack.peek());
			
			if (item == null) {
				throw new SVAbortException("Failed to find type for \"" + fResolveStack.peek().getType() + "\"");
			}
			fLog.debug("    item type: " + SVDBItem.getName(item));
			
			item = findInClassHierarchy((ISVDBChildItem)item, expr.getId());
			
			if (item == null) {
				throw new SVAbortException("Failed to find field \"" + expr.getId() + "\"");
			}
			
			fResolveStack.push(item);
		}
	}
	
	protected void tf_call(SVDBTFCallExpr expr) {
		if (fResolveStack.size() == 0) {
			// Resolve relative to the active context
		} else {
			// Resolve relative to the stack-top context
		}
	}

	protected void assign_expr(SVDBAssignExpr expr) {
		fLog.debug("assign_expr: ");
		visit(expr.getLhs());
		visit(expr.getRhs());
	}

}

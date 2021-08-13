/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.expr_utils;

import java.util.List;
import java.util.Stack;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInst;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInstItem;
import org.eclipse.hdt.sveditor.core.db.SVDBModportDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBPackageDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBParamValueAssignList;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfo;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfoUserDef;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBArrayAccessExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBAssignExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBCastExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBFieldAccessExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBIdentifierExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBParenExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBTFCallExpr;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.search.ISVDBFindNameMatcher;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByName;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByNameInClassHierarchy;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindByNameInScopes;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindNamedClass;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindParameterizedClass;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindSuperClass;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBTypedefStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDimItem;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.ILogLevelListener;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class SVContentAssistExprVisitor implements ILogLevel, ILogLevelListener {
	private LogHandle					fLog;
	private boolean						fDebugEn;
	private ISVDBIndexIterator			fIndexIt;
	private ISVDBScopeItem				fScope;
	private ISVDBChildItem				fClassScope;
	private ISVDBFindNameMatcher		fNameMatcher;
	private Stack<ISVDBItemBase>		fResolveStack;
	private SVDBFindNamedClass 			fFindNamedClass;
	private SVDBFindParameterizedClass	fFindParameterizedClass;
	private boolean						fStaticAccess;
	
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
		fLog.addLogLevelListener(this);
		logLevelChanged(fLog);
		fResolveStack = new Stack<ISVDBItemBase>();
		fScope = scope;
		fNameMatcher = name_matcher;
		fIndexIt = index_it;
		fFindNamedClass = new SVDBFindNamedClass(fIndexIt);
		fFindParameterizedClass = new SVDBFindParameterizedClass(fIndexIt);
		classifyScope();
	}
	
	
	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = (handle.getDebugLevel() > 0);
	}



	private void classifyScope() {
		ISVDBChildItem parent = fScope;
		
		fClassScope = null;
		
		if (fScope == null) {
			return;
		}
		
		while (parent != null && !parent.getType().isElemOf(
				SVDBItemType.ClassDecl, SVDBItemType.Covergroup
				)) { 
			parent = parent.getParent();
		}
		
		if (parent != null) {
			fClassScope = parent;
		} else {
			// See if this scope is an external task/function
			if (fScope.getType() == SVDBItemType.Function || 
					fScope.getType() == SVDBItemType.Task) {
				String name = ((SVDBTask)fScope).getName();
				int idx;
				if ((idx = name.indexOf("::")) != -1) {
					String class_name = name.substring(0, idx);
					if (fDebugEn) {
						fLog.debug("class_name: " + class_name);
					}
					List<SVDBClassDecl> result = fFindNamedClass.findItem(class_name);
					
					if (result.size() > 0) {
						fClassScope = result.get(0);
					}
				}
			}
		}
	}
	
	public ISVDBItemBase findItem(SVDBExpr expr) {
		if (fDebugEn) {
			fLog.debug("findItem");
		}
		fResolveStack.clear();
		
		try {
			visit(expr);
			if (fResolveStack.size() > 0) {
				return fResolveStack.pop();
			}
		} catch (SVAbortException e) {
			fLog.debug("findItem failed: " + e.getMessage(), e);
		}

		return null;
	}

	public ISVDBItemBase findTypeItem(SVDBExpr expr) {
		if (fDebugEn) {
			fLog.debug("findItemType: fScope=" + SVDBItem.getName(fScope));
		}
		fResolveStack.clear();
		
		try {
			visit(expr);
			if (fResolveStack.size() > 0) {
				return findType(fResolveStack.peek());
			}
		} catch (SVAbortException e) {
			fLog.debug("Failed to traverse expression", e);
		}

		return null;
	}

	protected void visit(SVDBExpr expr) {
		if (fDebugEn) {
			fLog.debug("visit: " + expr.getType());
		}
		switch (expr.getType()) {
				
			case CastExpr:
				cast_expr((SVDBCastExpr)expr);
				break;
				
			case FieldAccessExpr:
				field_access_expr((SVDBFieldAccessExpr)expr);
				break;
			
			case ParamIdExpr:
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
				
			case ArrayAccessExpr:
				array_access_expr((SVDBArrayAccessExpr)expr);
				break;
				

			case ClockingEventExpr:
			case ConcatenationExpr:
			case CondExpr:
			case CrossBinsSelectConditionExpr:
			case CtorExpr:
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
		if (fDebugEn) {
			fLog.debug("cast_expr: " + expr.getCastType().toString());
		}
		
	}

	protected void field_access_expr(SVDBFieldAccessExpr expr) {
		if (fDebugEn) {
			fLog.debug("field_access_expr: (" + (expr.isStaticRef()?"::":".") + ")");
		}
		visit(expr.getExpr());
 		fStaticAccess = expr.isStaticRef();
		visit(expr.getLeaf());
		fStaticAccess = false;
	}
	
	private ISVDBItemBase findInScopeHierarchy(String name) {
		SVDBFindByNameInScopes finder = new SVDBFindByNameInScopes(fIndexIt);
	
		if (fDebugEn) {
			fLog.debug("FindByNameInScopes: " + 
					((fScope != null)?(fScope.getType() + " " + SVDBItem.getName(fScope)):"NONE"));
		}
		List<ISVDBItemBase> items = finder.findItems(fScope, name, false);
		
		// Filter out the forward typedefs
		filterFwdDecls(items);
		
		if (items.size() > 0) {
			return items.get(0);
		} else {
			return null;
		}
	}
	
	private ISVDBItemBase findInClassHierarchy(ISVDBChildItem root, String name) {
		if (fDebugEn) {
			fLog.debug("findInClassHierarchy: " + root.getType() + " " + SVDBItem.getName(root) + " => " + name);
		}
		if (root.getType() == SVDBItemType.Covergroup) {
			// Find the built-in class
			if (fDebugEn) {
				fLog.debug("Search for covergroup class");
			}
			
			List<SVDBClassDecl> l = fFindNamedClass.findItem("__sv_builtin_covergroup");
			if (l.size() > 0) {
				root = l.get(0);
			} else {
				return null;
			}
		}
		
		SVDBFindByNameInClassHierarchy finder_h = 
			new SVDBFindByNameInClassHierarchy(fIndexIt, fNameMatcher);
		
		List<ISVDBItemBase> items = finder_h.find(root, name, 
				fStaticAccess, !fStaticAccess);

		// Filter out the forward typedefs
		filterFwdDecls(items);

		if (items.size() > 0) {
			return items.get(0);
		} else {
			return null;
		}
	}
	
	private ISVDBItemBase findInModuleInterface(SVDBModIfcDecl root, String name) {
		ISVDBItemBase ret = null;
		if (fDebugEn) {
			fLog.debug("findInModuleInterface: " + root.getType() + " " + SVDBItem.getName(root) + " => " + name);
		}
	
		for (ISVDBChildItem c : root.getChildren()) {
			if (fDebugEn) {
				fLog.debug("  item: " + c.getType() + " " + SVDBItem.getName(c));
			}
			if (c.getType() == SVDBItemType.VarDeclStmt) {
				for (ISVDBChildItem i : ((SVDBVarDeclStmt)c).getChildren()) {
					if (fNameMatcher.match((ISVDBNamedItem)i, name)) {
						ret = i;
						break;
					}
				}
			} else if (c.getType() == SVDBItemType.ModIfcInst) {
				for (ISVDBChildItem i : ((SVDBModIfcInst)c).getChildren()) {
					if (fNameMatcher.match((ISVDBNamedItem)i, name)) {
						ret = i;
						break;
					}
				}
			} else if (c.getType() == SVDBItemType.ModportDecl) {
				for (ISVDBChildItem i : ((SVDBModportDecl)c).getChildren()) {
					if (fNameMatcher.match((ISVDBNamedItem)i, name)) {
						ret = i;
						break;
					}
				}
			} else if (c instanceof ISVDBNamedItem) {
				if (fDebugEn) {
					fLog.debug("    Named Item");
				}
				if (fNameMatcher.match((ISVDBNamedItem)c, name)) {
					ret = c;
					break;
				}
			}
		}
		
		if (ret == null) {
			for (SVDBParamPortDecl p : root.getPorts()) {
				for (ISVDBChildItem i : p.getChildren()) {
					if (fNameMatcher.match((ISVDBNamedItem)i, name)) {
						ret = i;
						break;
					}
				}
			}
		}
	
		if (fDebugEn) {
			fLog.debug("<-- findInModuleInterface: " + ret);
		}
		
		return ret;
	}

	private ISVDBItemBase findInTypeInfo(SVDBTypeInfo root, String name) {
		if (fDebugEn) {
			fLog.debug("findInTypeInfo: " + root.getType() + " " + SVDBItem.getName(root) + " => " + name);
		}
		
		if (root.getType().isElemOf(SVDBItemType.TypeInfoStruct, SVDBItemType.TypeInfoUnion)) {
			ISVDBChildParent p = (ISVDBChildParent)root;
			
			for (ISVDBChildItem c : p.getChildren()) {
				if (c.getType() == SVDBItemType.VarDeclStmt) {
					for (ISVDBChildItem i : ((SVDBVarDeclStmt)c).getChildren()) {
						if (fNameMatcher.match((ISVDBNamedItem)i, name)) {
							return i;
						}
					}
				} else if (c instanceof ISVDBNamedItem) {
					if (fNameMatcher.match((ISVDBNamedItem)c, name)) {
						return c;
					}
				}
			}
		}
		
		return null;
	}
	
	private ISVDBItemBase findInPackage(SVDBPackageDecl pkg, String name) {
		ISVDBItemBase ret = null;
//		SVDBFile file = null;
		ISVDBChildItem c = pkg;
		
		while (c != null && c.getType() != SVDBItemType.PackageDecl) {
			c = c.getParent();
		}
		
		for (ISVDBChildItem pkg_item : pkg.getChildren()) {
			if (pkg_item.getType() == SVDBItemType.Include) {
				// TODO:
				// ret = findInInclude(file, pkg_item, name);
			} else if (SVDBItem.getName(pkg_item).equals(name)) {
				ret = pkg_item;
				break;
			}
		}
		
		return ret;
	}
	
	/**
	 * Returns the type of the specified element.  
	 * @param item
	 * @return
	 */
	private ISVDBItemBase findType(ISVDBItemBase item) {
		SVDBTypeInfo   type = null;
		List<SVDBVarDimItem> var_dim = null;
		if (fDebugEn) {
			fLog.debug("findType: " + item.getType() + " " + SVDBItem.getName(item));
		}
		
		if (item.getType() == SVDBItemType.VarDeclItem) {
			SVDBVarDeclItem var  = (SVDBVarDeclItem)item;
			SVDBVarDeclStmt stmt = var.getParent();
			
			var_dim = var.getArrayDim();
			type = stmt.getTypeInfo();
		} else if (item.getType() == SVDBItemType.ClassDecl) {
			// NULL transform: item is already a type
			if (fDebugEn) {
				fLog.debug("    item " + SVDBItem.getName(item) + " already a class");
			}
			return item;
		} else if (item.getType() == SVDBItemType.PackageDecl) {
			if (fDebugEn) {
				fLog.debug("    item " + SVDBItem.getName(item) + " is a package");
			}
			return item;
		} else if (item.getType() == SVDBItemType.ModIfcInstItem) {
			SVDBModIfcInstItem mod_ifc = (SVDBModIfcInstItem)item;
			SVDBModIfcInst mod_ifc_p = (SVDBModIfcInst)mod_ifc.getParent();

			type = mod_ifc_p.getTypeInfo();
		} else if (item.getType() == SVDBItemType.TypedefStmt) {
			type = ((SVDBTypedefStmt)item).getTypeInfo();
		}
		
		if (type != null) {
			if (fDebugEn) {
				fLog.debug("    type is non-null: " + type.getType());
			}
			if (type.getType() == SVDBItemType.TypeInfoUserDef) {
				item = findTypedef(item, type.getName());
			} else if (type.getType() == SVDBItemType.TypeInfoModuleIfc) {
				item = findTypedef(null, type.getName());
			} else if (type.getType().isElemOf(SVDBItemType.TypeInfoStruct, SVDBItemType.TypeInfoUnion)) {
				item = type;
			}
			
			// Resolve any typedefs
			item = resolveTypedefs(item);
			
			if (var_dim != null) {
				// TODO: should probably handle non-user base types
				if (item != null) {
					// TODO: handle multi-dim arrays?
					item = resolveArrayType(item, SVDBItem.getName(item), var_dim.get(0));
				}
			}
		} else {
			if (fDebugEn) {
				fLog.debug("  type is null");
			}
		}
	
		if (fDebugEn) {
			fLog.debug("<-- findType: " + ((item!=null)?SVDBItem.getName(item):"NULL"));
		}
		return item;
	}
		
	private ISVDBItemBase findTypedef(ISVDBItemBase root, String name) {
		ISVDBItemBase ret = null;
		
		fLog.debug("--> findTypedef: " + name);
		/*
		if ((ret = findLocalTypedef(name)) == null) {
			// Look globally
			SVDBFindByName finder_n = new SVDBFindByName(fIndexIt);

			List<ISVDBItemBase> item_l = finder_n.find(name);

			// Filter out the forward typedefs
			filterFwdDecls(item_l);

			if (item_l.size() > 0) {
				ret = item_l.get(0);
			}
		}
		 */

		if (name.indexOf('.') != -1) {
			String type_elems[] = name.split("\\.");
		
			ISVDBItemBase type_root = findRoot(type_elems[0]);
			fLog.debug("   Root type: " + type_root);
			if (type_root != null) {
				int start_size = fResolveStack.size();
				fResolveStack.push(type_root);
				identifier_expr(new SVDBIdentifierExpr(type_elems[1]));
				int end_size = fResolveStack.size();
				
				fLog.debug("start_size=" + start_size + " end_size=" + end_size);
				if (end_size > (start_size+1)) {
					ret = fResolveStack.peek();
					fResolveStack.setSize(start_size);
				}
			}
			// Scoped type
			fLog.debug("  [TODO] Handle scoped type \"" + name + "\"");
		} else {
			
			ret = findLocalTypedef(fScope, name);
		
			// Search relative to the target variable
			if (ret == null && root != null && 
					root.getType() == SVDBItemType.VarDeclItem) {
				SVDBVarDeclStmt var_stmt = ((SVDBVarDeclItem)root).getParent();
				
				if (var_stmt.getParent() != null && 
						var_stmt.getParent().getType() == SVDBItemType.ClassDecl) {
					fLog.debug("Could search declaration context");
					ISVDBChildParent cls_scope = (ISVDBChildParent)var_stmt.getParent();
					ret = findLocalTypedef(cls_scope, name);
				}
			}
			
			if (ret == null) {
				// Look globally

				ret = findGlobalType(name);
			}
		}
		
		fLog.debug("<-- findTypedef: " + ((ret != null)?SVDBItem.getName(ret):"null"));
		return ret;
	}
	
	private ISVDBItemBase findGlobalType(String name) {
		ISVDBItemBase ret = null;
		SVDBFindByName finder_n = new SVDBFindByName(fIndexIt);

		List<ISVDBItemBase> item_l = finder_n.findItems(name);
		
		// Filter out the forward typedefs
		filterFwdDecls(item_l);

		if (item_l.size() > 0) {
			ret = item_l.get(0);
			
			// Resolve typedefs
			ret = resolveTypedefs(ret);
		}
		
		return ret;
	}
	
	private ISVDBItemBase resolveTypedefs(ISVDBItemBase item ) {
		while (item != null && item.getType() == SVDBItemType.TypedefStmt) {
			fLog.debug("Item " + SVDBItem.getName(item) + " is typedef");
			SVDBTypedefStmt td = (SVDBTypedefStmt)item;
			SVDBTypeInfo type = td.getTypeInfo();
			if (type.getType().isElemOf(SVDBItemType.TypeInfoStruct, SVDBItemType.TypeInfoUnion)) {
				// Found something useful
				item = type;
			} else if (type.getType() == SVDBItemType.TypeInfoUserDef) {
				// Lookup user-defined type name
				item = findTypedef(null, type.getName());
			} else {
				// gone as far as we can go
				break;
			}
		}
		
		return item;
	}
	
	private ISVDBItemBase findLocalTypedef(ISVDBChildParent init_scope, String name) {
		ISVDBItemBase ret = null;
		fLog.debug("--> findLocalTypedef: " + name);
		
		ISVDBChildParent scope = init_scope;
		
		while (scope != null && scope.getType() != SVDBItemType.File) {
			fLog.debug("  search scope " + SVDBItem.getName(scope));
			for (ISVDBChildItem c : scope.getChildren()) {
				if (c.getType() == SVDBItemType.TypedefStmt &&
						SVDBItem.getName(c).equals(name)) {
					// TODO: should probably filter out forward declarations
					ret = c;
				}
			}
			
			// Skip over non-parent scopes
			ISVDBChildItem c = scope;
			while ((c = c.getParent()) != null && !(c instanceof ISVDBChildParent)) { }
		
			if (c != null) {
				scope = (ISVDBChildParent)c;
			} else {
				scope = null;
			}
		}
		
		fLog.debug("<-- findLocalTypedef: " + SVDBItem.getName(ret));
		return ret;
	}
	
	private ISVDBItemBase resolveArrayType(ISVDBItemBase base, String base_type, SVDBVarDimItem var_dim) {
		ISVDBItemBase ret = null;
		SVDBTypeInfoUserDef target_type_info = null;
		SVDBParamValueAssignList param_l = new SVDBParamValueAssignList();
		
		fLog.debug("resolveArrayType: " + base + " " + base_type);
		
		switch (var_dim.getDimType()) {
			case Associative:
				fLog.debug("Associative array");
				target_type_info = new SVDBTypeInfoUserDef("__sv_builtin_assoc_array");
				param_l.addParameter("T", base_type);
				param_l.addParameter("IDX", var_dim.getExpr().toString());
				break;
			case Queue:
				fLog.debug("Queue");
				target_type_info = new SVDBTypeInfoUserDef("__sv_builtin_queue");
				param_l.addParameter("T", base_type);
				break;
			case Sized:
			case Unsized:
				fLog.debug("Array");
				target_type_info = new SVDBTypeInfoUserDef("__sv_builtin_array");
				param_l.addParameter("T", base_type);
				break;
			default:
				fLog.debug("Unknown variable dimension type");
					
		}
		
		target_type_info.setParameters(param_l);
		
		// Locate the class
		ret = fFindParameterizedClass.find(target_type_info);
		
		if (ret == null) {
			fLog.debug("Failed to find target_type_info: " + target_type_info.getName());
		}

		/*
		System.out.println("    resolveArrayType: ret=" + ret);
		for (ISVDBItemBase b : ((SVDBClassDecl)ret).getItems()) {
			System.out.println("    " + SVDBItem.getName(b));
		}
		 */

		return ret;
	}
	
	private ISVDBItemBase findRoot(String id) {
		ISVDBItemBase ret = null;
		fLog.debug("findRoot: " + id);

		if (id.equals("this") || id.equals("super")) {
			if (fClassScope != null) {
				if (id.equals("this")) {
					return fClassScope;
				} else if (fClassScope.getType() == SVDBItemType.ClassDecl) {
					SVDBFindSuperClass finder = new SVDBFindSuperClass(fIndexIt);
					return finder.find((SVDBClassDecl)fClassScope);
				}
			} else {
				return null;
			}
		}
		
		// Check up the scopes in this class/module/interface
		if ((ret = findInScopeHierarchy(id)) != null) {
			return ret;
		}
		
		// Check the super-class hierarchy
		if (fClassScope != null && (ret = findInClassHierarchy(fClassScope, id)) != null) {
			return ret;
		}
		
		// Perform global search
		List<SVDBClassDecl> cls_l = fFindNamedClass.findItem(id);
		
		if (cls_l.size() > 0) {
			return cls_l.get(0);
		}
		
		SVDBFindByName name_finder = new SVDBFindByName(fIndexIt);
		List<ISVDBItemBase> item_l = name_finder.findItems(id);
		
		// Filter out the forward typedefs
		filterFwdDecls(item_l);

		if (item_l.size() > 0) {
			return item_l.get(0);
		}

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
			fLog.debug("Resolve : " + expr.getId() + " relative to " + 
					fResolveStack.peek() + " " + SVDBItem.getName(fResolveStack.peek()));
			ISVDBItemBase item = findType(fResolveStack.peek());
			
			if (item == null) {
				throw new SVAbortException("Failed to find type for \"" + fResolveStack.peek().getType() + "\"");
			}
			fLog.debug("    item type: " + SVDBItem.getName(item));
			
			if (item.getType() == SVDBItemType.PackageDecl) {
				item = findInPackage((SVDBPackageDecl)item, expr.getId());
			} else if (item.getType().isElemOf(SVDBItemType.TypeInfoStruct, SVDBItemType.TypeInfoUnion)) {
				item = findInTypeInfo((SVDBTypeInfo)item, expr.getId());
			} else if (item.getType() == SVDBItemType.ModuleDecl ||
					item.getType() == SVDBItemType.InterfaceDecl) {
				item = findInModuleInterface((SVDBModIfcDecl)item, expr.getId());
			} else if (item.getType() == SVDBItemType.ModportItem) {
				// TODO: find in modport
			} else {
				item = findInClassHierarchy((ISVDBChildItem)item, expr.getId());
			}
			
			if (item == null) {
				// Try a global type search
				item = findGlobalType(expr.getId());
			}
			
			if (item == null) {
				throw new SVAbortException("Failed to find field \"" + expr.getId() + "\"");
			}
			
			fResolveStack.push(item);
		}
	}
	
	protected void tf_call(SVDBTFCallExpr expr) {
		fLog.debug("tf_call: ");
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
	
	protected void array_access_expr(SVDBArrayAccessExpr expr) {
		fLog.debug("array_access_expr: ");
		visit(expr.getLhs());
		
		if (fResolveStack.size() == 0) {
			throw new SVAbortException("Incorrect array-access expression at root");
		}
		ISVDBItemBase item = fResolveStack.peek();
		fLog.debug("item=" + item.getType());
		
		if (item.getType() == SVDBItemType.VarDeclItem) {
			// Push a non-array version of the variable
			SVDBVarDeclItem vi = ((SVDBVarDeclItem)item).duplicate();
			vi.setArrayDim(null);
			fResolveStack.push(vi);
		}
	}

	protected void filterFwdDecls(List<ISVDBItemBase> items) {
		for (int i=0; i<items.size(); i++) {
			if (items.get(i).getType() == SVDBItemType.TypedefStmt) {
				SVDBTypedefStmt td = (SVDBTypedefStmt)items.get(i);
				if (td.getTypeInfo().getType() != null &&
						td.getTypeInfo().getType() == SVDBItemType.TypeInfoFwdDecl) {
					items.remove(i);
					i--;
				}
			}
		}
	}
}

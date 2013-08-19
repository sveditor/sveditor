/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.content_assist;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBInterfaceDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModportDecl;
import net.sf.sveditor.core.db.SVDBModportItem;
import net.sf.sveditor.core.db.SVDBModportPortsDecl;
import net.sf.sveditor.core.db.SVDBModportSimplePort;
import net.sf.sveditor.core.db.SVDBModportSimplePortsDecl;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIncFileInfo;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameInClassHierarchy;
import net.sf.sveditor.core.db.search.SVDBFindByNameInScopes;
import net.sf.sveditor.core.db.search.SVDBFindByNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindContentAssistNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVContentAssistExprVisitor;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprContext.ContextType;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.expr_utils.SVExprUtilsParser;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

import org.eclipse.core.runtime.NullProgressMonitor;


public abstract class AbstractCompletionProcessor implements ILogLevel {
//	protected List<SVCompletionProposal>		fCompletionProposals;
	protected Map<Integer, List<SVCompletionProposal>>		fCompletionProposalMap;
	protected List<SVCompletionProposal>					fCompletionProposals;
	
	protected LogHandle							fLog;
	/**
	private static final String 				fBuiltInMacroProposals[] = { 
		"define", "include" 
	};
	 */
	
	public AbstractCompletionProcessor() {
		fCompletionProposalMap = new HashMap<Integer, List<SVCompletionProposal>>();
	}
	
	protected abstract ISVDBIndexIterator getIndexIterator();
	
	protected abstract SVDBFile getSVDBFile();
	
	protected void addProposal(SVCompletionProposal p) {
		boolean found = false;
	
		synchronized (fCompletionProposalMap) {
			for (Integer priority : fCompletionProposalMap.keySet()) {
				for (SVCompletionProposal p_t : fCompletionProposalMap.get(priority)) {
					if (p_t.equals(p)) {
						found = true;
						break;
					}
				}
				if (found) {
					break;
				}
			}

			if (!found) {
				if (!fCompletionProposalMap.containsKey(p.getPriorityCategory())) {
					fCompletionProposalMap.put(p.getPriorityCategory(), 
							new ArrayList<SVCompletionProposal>());
				}
				fLog.debug(LEVEL_MID, "addProposal \"" + p.getReplacement() + "\": category=" + 
						p.getPriorityCategory() + " priority=" + p.getPriority());
				fCompletionProposalMap.get(p.getPriorityCategory()).add(p);
			}
		}
	}
	
	public List<SVCompletionProposal> getCompletionProposals() {
		if (fCompletionProposals != null) {
			return fCompletionProposals;
		} else {
			return new ArrayList<SVCompletionProposal>();
		}
	}

	public void computeProposals(
			IBIDITextScanner 	scanner,
			SVDBFile			active_file,
			int					lineno) {
		computeProposals(scanner, active_file, lineno, -1);
	}

	public void computeProposals(
			IBIDITextScanner 	scanner,
			SVDBFile			active_file,
			int					lineno,
			int					linepos) {
		SVExprScanner expr_scan = new SVExprScanner();
	
		synchronized (fCompletionProposalMap) {
			fCompletionProposalMap.clear();
		}
		
		// Trigger characters and string prior to the trigger (if any)

		fLog.debug(LEVEL_MID, 
				"computeProposals: " + 
						active_file.getFilePath() + ":" + lineno + ":" + linepos);
				
		ISVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				active_file, lineno);
		
		if (src_scope != null) {
			fLog.debug(LEVEL_MID, "src_scope: " + src_scope.getType() + " " + SVDBItem.getName(src_scope));
		} else {
			fLog.debug(LEVEL_MID, "failed to find source scope");
		}

		SVExprContext ctxt = expr_scan.extractExprContext(scanner, false);
		fLog.debug(LEVEL_MID, "ctxt: type=" + ctxt.fType + 
				" trigger=" + ctxt.fTrigger + " root=" + ctxt.fRoot + 
				" leaf=" + ctxt.fLeaf + " start=" + ctxt.fStart);

		if (ctxt.fTrigger != null) {
			if (ctxt.fTrigger.equals("`")) {
				findMacroItems(ctxt, getIndexIterator());
			} else if (ctxt.fRoot != null &&
					(ctxt.fTrigger.equals("=") || ctxt.fTrigger.equals(".") || 
							ctxt.fTrigger.equals("::") || ctxt.fTrigger.equals(":"))) {
				if (ctxt.fTrigger.equals(".") || ctxt.fTrigger.equals("::")) {
					SVDBExpr expr = null;
					SVExprUtilsParser parser = new SVExprUtilsParser(ctxt);
					try {
						expr = parser.parsers().exprParser().expression();
					} catch (SVParseException e) {
						fLog.debug(LEVEL_MID, "Failed to parse the content-assist expression", e);
						return;
					}

					// Traverse the expression to find the type of the root element 
					SVContentAssistExprVisitor v = new SVContentAssistExprVisitor(
							src_scope, SVDBFindDefaultNameMatcher.getDefault(), getIndexIterator());
					ISVDBItemBase item = null;
					if (expr != null) {
						item = v.findTypeItem(expr);
					}

					if (item == null) {
						fLog.debug(LEVEL_MID, "Failed to traverse the content-assist expression (" +
								fCompletionProposalMap.size() + ")");
						/*
						if (fCompletionProposals.size() > 0) {
							System.out.println("" + fCompletionProposals.get(0) + ";" + 
									fCompletionProposals.get(0).getReplacement() + ";" +
									fCompletionProposals.get(0).getItem());
						}
						 */
						return;
					}
					fLog.debug(LEVEL_MID, "Item: " + item.getType() + " " + SVDBItem.getName(item));

					// '.' or '::' trigger
					findTriggeredProposals(ctxt, src_scope, item);
				} else if (ctxt.fTrigger.equals("=")) {
					// '=' trigger
					SVDBExpr expr = null;
					SVExprUtilsParser parser = new SVExprUtilsParser(ctxt);
					try {
						expr = parser.parsers().exprParser().expression();
					} catch (SVParseException e) {
						fLog.debug(LEVEL_MID, "Failed to parse the content-assist expression", e);
						return;
					}

					// Traverse the expression to find the type of the root element 
					SVContentAssistExprVisitor v = new SVContentAssistExprVisitor(
							src_scope, SVDBFindDefaultNameMatcher.getDefault(), getIndexIterator());
					ISVDBItemBase item = null;
					if (expr != null) {
						try {
							item = v.findTypeItem(expr);
						} catch (RuntimeException e) {
							// it's okay to ignore this, since it only might be helpful
						}
					}

					if (item == null) {
						fLog.debug(LEVEL_MID, "Failed to traverse the content-assist expression");
					}
					fLog.debug(LEVEL_MID, "Item: " + ((item != null)?(item.getType() + " " + SVDBItem.getName(item)):"null"));
					
					findAssignTriggeredProposals(ctxt, src_scope, item);
				} else if (ctxt.fTrigger.equals(":")) {
					// Trigger of ':' occurs when the user wishes content assist for 
					// a labeled 
					if (ctxt.fRoot.startsWith("end")) {
						findEndLabelProposals(ctxt, src_scope);
					} else {
						// default to suggesting globals
						findUntriggeredProposals(ctxt, src_scope);
					}
				} else {
					// Unknown trigger
				}
			} else if (ctxt.fTrigger.equals(".")) {
				// null root and '.' -- likely a port completion
				fLog.debug(LEVEL_MID, "likely port completion");

				findPortCompletionProposals(ctxt, src_scope, lineno, linepos);
			} else {
				// Unknown trigger
			}
		} else {
			// Trigger is null
			findUntriggeredProposals(ctxt, src_scope);
		}

		fCompletionProposals = order_proposals(ctxt.fLeaf, fCompletionProposalMap);
	}
	
	private void findTriggeredProposals(
			SVExprContext			ctxt,
			ISVDBChildItem			src_scope,
			ISVDBItemBase			leaf_item) {
		boolean static_ref = ctxt.fTrigger.equals("::");
		// Determine the type of the leaf item
		fLog.debug("findTriggeredProposals: " + leaf_item.getType());
		
		// Search up hierarchy ?
		if (leaf_item.getType() == SVDBItemType.ClassDecl ||
				leaf_item.getType() == SVDBItemType.TypeInfoStruct ||
				leaf_item.getType() == SVDBItemType.InterfaceDecl ||
				leaf_item.getType() == SVDBItemType.ModuleDecl) {
			// Look for matching names in the target class
			SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
			SVDBFindSuperClass super_finder = new SVDBFindSuperClass(getIndexIterator()/*, matcher*/);
			ISVDBChildParent si = (ISVDBChildParent)leaf_item;
			int scope_level = 0;
			
			while (si != null) {
				for (ISVDBChildItem it : si.getChildren()) {
					if (it.getType() == SVDBItemType.VarDeclStmt) {
						SVDBVarDeclStmt v = (SVDBVarDeclStmt)it;
						// Ensure static ref is correct
						if ((v.getAttr() & SVDBVarDeclStmt.FieldAttr_Static) != 0 == static_ref) {
							for (ISVDBItemBase it_1 : ((SVDBVarDeclStmt)it).getChildren()) {
								debug("VarDeclItem: " + SVDBItem.getName(it_1));
								if (matcher.match((ISVDBNamedItem)it_1, ctxt.fLeaf)) {
									addProposal(it_1, ctxt.fLeaf, scope_level, 
											SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
											true, ctxt.fStart, ctxt.fLeaf.length());
								}
							}
						}
					} else if (it.getType() == SVDBItemType.TypedefStmt) {
						SVDBTypedefStmt td_stmt = (SVDBTypedefStmt)it;
						if (matcher.match(td_stmt, ctxt.fLeaf)) {
							addProposal(td_stmt, ctxt.fLeaf, scope_level,
									SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
									true, ctxt.fStart, ctxt.fLeaf.length());
						}
						if (td_stmt.getTypeInfo() != null && 
								td_stmt.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
							SVDBTypeInfoEnum enum_type = (SVDBTypeInfoEnum)td_stmt.getTypeInfo();
							// Match against enumerators
							for (SVDBTypeInfoEnumerator enumerator : enum_type.getEnumerators()) {
								if (matcher.match(enumerator, ctxt.fLeaf)) {
									addProposal(enumerator, ctxt.fLeaf, scope_level,
											SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
											true, ctxt.fStart, ctxt.fLeaf.length());
								}
							}
						}
					} else if (it.getType() == SVDBItemType.ModportDecl) {
						for (ISVDBItemBase it_1 : ((SVDBModportDecl)it).getChildren()) {
							debug("ModportItem: " + SVDBItem.getName(it_1));
							if (matcher.match((ISVDBNamedItem)it_1, ctxt.fLeaf)) {
								// TODO: is this really category behavioral-scope?
								addProposal(it_1, ctxt.fLeaf, scope_level,
										SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
										true, ctxt.fStart, ctxt.fLeaf.length());
							}
						}
					} else if (it.getType() == SVDBItemType.ModIfcInst) {
						for (ISVDBItemBase it_1 : ((SVDBModIfcInst)it).getChildren()) {
							if (matcher.match((ISVDBNamedItem)it_1, ctxt.fLeaf)) {
								// TODO: is this really category behavioral-scope?
								addProposal(it_1, ctxt.fLeaf, scope_level,
										SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
										true, ctxt.fStart, ctxt.fLeaf.length());
							}
						}
					} else if (it instanceof ISVDBNamedItem) {
						if (matcher.match((ISVDBNamedItem)it, ctxt.fLeaf)) {
							addProposal(it, ctxt.fLeaf, scope_level,
									SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
									true, ctxt.fStart, ctxt.fLeaf.length());
						}
					}
				}
				
				if (si.getType() == SVDBItemType.ClassDecl) {
					SVDBClassDecl cls_decl = (SVDBClassDecl)si;
					si = super_finder.find(cls_decl);
				} else {
					if (si.getType().isElemOf(SVDBItemType.InterfaceDecl)) {
						// Search the ports of the interface handle
						SVDBInterfaceDecl ifc = (SVDBInterfaceDecl)si;

						for (SVDBParamPortDecl p : ifc.getPorts()) {
							for (ISVDBItemBase vi : p.getChildren()) {
								if (matcher.match((ISVDBNamedItem)vi, ctxt.fLeaf)) {
									addProposal(vi, ctxt.fLeaf, scope_level,
											SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
											true, ctxt.fStart, ctxt.fLeaf.length());
								}
							}
						}
					}
					si = null;
				}
				scope_level++;
			}
		} else if (leaf_item.getType() == SVDBItemType.PackageDecl) {
			SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
			if (!static_ref) {
				fLog.debug("Warning: non-static reference to package type");
			}
		
			ISVDBIndexIterator index_it = getIndexIterator();
	
			SVDBPackageDecl pkg_decl = (SVDBPackageDecl)leaf_item;
			List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(
					new NullProgressMonitor(), pkg_decl.getName(), 
					new SVDBFindByNameMatcher(SVDBItemType.PackageDecl));
			
			if (result.size() > 0) {
				SVDBDeclCacheItem pkg_item = result.get(0);
				List<SVDBDeclCacheItem> pkg_items = index_it.findPackageDecl(new NullProgressMonitor(), pkg_item);
				
				for (SVDBDeclCacheItem ci : pkg_items) {
					ISVDBItemBase item = ci.getSVDBItem();
					if (item.getType() == SVDBItemType.TypedefStmt) {
						SVDBTypedefStmt td_stmt = (SVDBTypedefStmt)item;
						if (matcher.match(td_stmt, ctxt.fLeaf)) {
							addProposal(td_stmt, ctxt.fLeaf, 0,
									SVCompletionProposal.PRIORITY_PACKAGE_SCOPE,
									true, ctxt.fStart, ctxt.fLeaf.length());
						}
						if (td_stmt.getTypeInfo() != null && 
								td_stmt.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
							SVDBTypeInfoEnum enum_type = (SVDBTypeInfoEnum)td_stmt.getTypeInfo();
							// Match against enumerators
							for (SVDBTypeInfoEnumerator enumerator : enum_type.getEnumerators()) {
								if (matcher.match(enumerator, ctxt.fLeaf)) {
									addProposal(enumerator, ctxt.fLeaf, 0,
											SVCompletionProposal.PRIORITY_PACKAGE_SCOPE,
											true, ctxt.fStart, ctxt.fLeaf.length());
								}
							}
						}						
					} else if (item instanceof ISVDBNamedItem) {
						ISVDBNamedItem ni = (ISVDBNamedItem)item;
						fLog.debug("Note: checking package item \"" + ni.getName() + "\"");
						if (matcher.match(ni, ctxt.fLeaf)) {
							addProposal(item, ctxt.fLeaf, 0,
									SVCompletionProposal.PRIORITY_PACKAGE_SCOPE,
									true, ctxt.fStart, ctxt.fLeaf.length());
						}
					} else {
						fLog.debug("Note: checking package item is not named item " +
								SVDBItem.getName(item));
					}
				}

			} else {
				fLog.debug("Failed to find package declaration \"" + pkg_decl.getName() + "\"");
			}
			System.out.println("Package Decl");
			
		} else if (leaf_item.getType() == SVDBItemType.VarDeclItem) {
			// Get the field type
			ISVDBItemBase item_type = getItemType(leaf_item);

			if (item_type != null && item_type.getType().isElemOf(SVDBItemType.ClassDecl)) {
				// Look for matching names in the target class
				ISVDBScopeItem si = (ISVDBScopeItem)item_type;
				SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
				
				for (ISVDBItemBase it : si.getChildren()) {
					if (it.getType() == SVDBItemType.VarDeclStmt) {
						for (ISVDBItemBase it_1 : ((SVDBVarDeclStmt)it).getChildren()) {
							debug("VarDeclItem: " + SVDBItem.getName(it_1));
							if (matcher.match((ISVDBNamedItem)it_1, ctxt.fLeaf)) {
								addProposal(it_1, ctxt.fLeaf, 0,
										SVCompletionProposal.PRIORITY_CLS_HIERARCHY_SCOPE,
										true, ctxt.fStart, ctxt.fLeaf.length());
							}
						}
					} else if (it instanceof ISVDBNamedItem) {
						if (matcher.match((ISVDBNamedItem)it, ctxt.fLeaf)) {
							addProposal(it, ctxt.fLeaf, 0,
									SVCompletionProposal.PRIORITY_CLS_HIERARCHY_SCOPE,
									true, ctxt.fStart, ctxt.fLeaf.length());
						}
					}
				}
			}
		} else if (leaf_item.getType() == SVDBItemType.ModportItem) {
			SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
			SVDBModportItem mpi = (SVDBModportItem)leaf_item;
			for (SVDBModportPortsDecl pd : mpi.getPortsList()) {
				if (pd.getType() == SVDBItemType.ModportSimplePortsDecl) {
					SVDBModportSimplePortsDecl simple_pd = (SVDBModportSimplePortsDecl)pd;
					for (SVDBModportSimplePort p : simple_pd.getPortList()) {
						if (matcher.match(p, ctxt.fLeaf)) {
							addProposal(p, ctxt.fLeaf, 0,
									SVCompletionProposal.PRIORITY_MOD_IFC_CLS_SCOPE,
									true, ctxt.fStart, ctxt.fLeaf.length());
						}
					}
				} else {
					fLog.debug(LEVEL_MIN, "Unhandled mod-port type " + pd.getType());
				}
			}
		}
	}
	
	private void findAssignTriggeredProposals(
			SVExprContext			ctxt,
			ISVDBChildItem			src_scope,
			ISVDBItemBase			item) {
		fLog.debug("Looking for assign-triggered identifier \"" + ctxt.fLeaf + "\"");
		List<ISVDBItemBase> result = new ArrayList<ISVDBItemBase>();
		SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
	
		FindByNameInScopes finder_s = new FindByNameInScopes(
				ctxt, getIndexIterator(), matcher);

		finder_s.findItems(src_scope, ctxt.fLeaf, false);

		FindByNameInClassHierarchy finder_h = new FindByNameInClassHierarchy(
				ctxt, getIndexIterator(), matcher);

		finder_h.find(src_scope, ctxt.fLeaf);

// Result is already added
//		result.addAll(tmp);

		// TODO:
		if (result.size() > 0) {
			for (int i=0; i<result.size(); i++) {
				boolean add = true;
				
				if (result.get(i).getType() == SVDBItemType.Function &&
						((ISVDBNamedItem)result.get(i)).getName().equals("new")) {
					add = false;
				}
				
				if (add) {
					addProposal(result.get(i), ctxt.fLeaf, 0,
							SVCompletionProposal.PRIORITY_GLOBAL_SCOPE,
							true, ctxt.fStart, ctxt.fLeaf.length());
				}
			}
		}

		// Try type names
		SVDBFindNamedModIfcClassIfc finder_cls =
			new SVDBFindNamedModIfcClassIfc(getIndexIterator(), matcher);

		List<ISVDBChildItem> cl_l = finder_cls.findItems(ctxt.fLeaf);

		if (cl_l.size() > 0) {
			fLog.debug("Global type search for \"" + ctxt.fLeaf + 
					"\" returned " + cl_l.size());
			for (ISVDBChildItem cl : cl_l) {
				fLog.debug("    " + cl.getType() + " " + SVDBItem.getName(cl));
			}
			
			for (ISVDBItemBase it : cl_l){
				addProposal(it, ctxt.fLeaf, 0,
						SVCompletionProposal.PRIORITY_GLOBAL_SCOPE,
						true, ctxt.fStart, ctxt.fLeaf.length());
			}
		} else {
			fLog.debug("Global class find for \"" + ctxt.fLeaf + 
			"\" returned no results");
		}

		// Try global task/function
		SVDBFindByName finder_tf = new SVDBFindByName(getIndexIterator(), matcher);

		List<ISVDBItemBase> it_l = finder_tf.findItems(ctxt.fLeaf);
		
		// Remove any definitions of extern tasks/functions, 
		// since the name prefix was incorrectly matched
		for (int i=0; i<it_l.size(); i++) {
			if (it_l.get(i).getType() == SVDBItemType.Function || 
					it_l.get(i).getType() == SVDBItemType.Task) {
				SVDBTask tf = (SVDBTask)it_l.get(i);
				if ((tf.getAttr() & IFieldItemAttr.FieldAttr_Extern) == 0 &&
						tf.getName().contains("::")) {
					it_l.remove(i);
					i--;
				}
				
				// Do not include tasks/functions unless they are completely
				// global or members of a package
				ISVDBItemBase scope_t = tf;
				while (scope_t != null && 
						scope_t.getType() != SVDBItemType.ClassDecl &&
						scope_t.getType() != SVDBItemType.ModuleDecl) {
					scope_t = ((ISVDBChildItem)scope_t).getParent();
				}

				if (scope_t != null && 
						(scope_t.getType() == SVDBItemType.ClassDecl ||
						scope_t.getType() == SVDBItemType.ModuleDecl)) {
					it_l.remove(i);
					i--;
				}
			}
		}
		
		if (it_l != null && it_l.size() > 0) {
			fLog.debug("Global find-by-name \"" + ctxt.fLeaf + "\" returned:");
			for (ISVDBItemBase it : it_l) {
				fLog.debug("    " + it.getType() + " " + ((ISVDBNamedItem)it).getName());
			}

			// TODO: Tag with priority
			for (ISVDBItemBase it : it_l) {
				addProposal(it, ctxt.fLeaf, 0,
						SVCompletionProposal.PRIORITY_GLOBAL_SCOPE,
						true, ctxt.fStart, ctxt.fLeaf.length());
			}
		} else {
			fLog.debug("Global find-by-name \"" + ctxt.fLeaf + 
			"\" (1) returned no results");
		}
		
		// Special case: If this is a constructor call, then do a 
		// context lookup on the LHS
		fLog.debug("item is type " + ((item != null)?item.getType():"null"));
		if (item != null && (item.getType() == SVDBItemType.ClassDecl) &&
				("new".startsWith(ctxt.fLeaf) || ctxt.fLeaf.equals(""))) {
			SVDBClassDecl cls = (SVDBClassDecl)item;
			
			fLog.debug("Looking for 'new' in root=" + SVDBItem.getName(item));
			for (ISVDBChildItem c : cls.getChildren()) {
				if (c.getType() == SVDBItemType.Function) {
					SVDBFunction f = (SVDBFunction)c;
					if (f.getName().equals("new")) {
						addProposal(c, ctxt.fLeaf, 0,
								SVCompletionProposal.PRIORITY_CLS_HIERARCHY_SCOPE,
								true, ctxt.fStart, ctxt.fLeaf.length());
					}
				}
			}
		}
	}
	
	private void findPortCompletionProposals(
			SVExprContext			ctxt,
			ISVDBChildParent		src_scope,
			int						lineno,
			int						linepos) {
		fLog.debug("--> findPortCompletionProposals:");
		SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
		// TODO: only provide content assist if we are in a module/interface scope
		fLog.debug("1");
		if (src_scope == null || 
				(src_scope.getType() != SVDBItemType.ModuleDecl &&
				src_scope.getType() != SVDBItemType.InterfaceDecl)) {
			fLog.debug("Return due to src_scope not Module or Interface (" + src_scope + ")");
			return;
		}
		fLog.debug("2");
		// First, need to find module/interface instance in question
		SVDBModIfcInst inst = findInst(src_scope, lineno, linepos);
		
		fLog.debug("3");
		if (inst == null) {
			fLog.debug("failed to find target module/interface instantiation");
			return;
		}
		
		fLog.debug("4");
		fLog.debug("instance type: " + inst.getTypeName());
		
		SVDBModIfcDecl decl;
		SVDBFindNamedModIfcClassIfc finder = new SVDBFindNamedModIfcClassIfc(getIndexIterator());
		List<ISVDBChildItem> result = finder.findItems(inst.getTypeName());
		
		if (result.size() > 0 && 
				(result.get(0).getType() == SVDBItemType.ModuleDecl ||
				result.get(0).getType() == SVDBItemType.InterfaceDecl)) {
			decl = (SVDBModIfcDecl)result.get(0); 
		} else {
			fLog.debug("failed to find module type \"" + inst.getTypeName() + "\"");
			return;
		}
		
		for (SVDBParamPortDecl p : decl.getPorts()) {
			for (ISVDBChildItem pi : p.getChildren()) {
				if (matcher.match((ISVDBNamedItem)pi, ctxt.fLeaf)) {
					addProposal(pi, ctxt.fLeaf, 0,
							SVCompletionProposal.PRIORITY_MOD_IFC_CLS_SCOPE,
							true, ctxt.fStart, ctxt.fLeaf.length());
				}
			}
		}
		fLog.debug("<-- findPortCompletionProposals:");
	}
	
	private SVDBModIfcInst findInst(ISVDBChildParent p, int lineno, int linepos) {
		SVDBModIfcInst last_inst = null;
		
		for (ISVDBChildItem c : p.getChildren()) {
			if (c.getType() == SVDBItemType.ModIfcInst) {
				last_inst = (SVDBModIfcInst)c;
				if (c.getLocation().getLine() > lineno) {
					break;
				}
			} else if (c instanceof ISVDBChildParent) {
				// We're done if the start of this scope is beyond our current line
				if (c.getLocation() != null && c.getLocation().getLine() > lineno) {
					break;
				}
				if ((last_inst = findInst((ISVDBChildParent)c, lineno, linepos)) != null) {
					break;
				}
			}
		}
		
		return last_inst;
	}

	private void findEndLabelProposals(
			SVExprContext			ctxt,
			ISVDBChildItem			src_scope) {
		fLog.debug("Looking for end-label proposal \"" + ctxt.fLeaf + "\"");
		fLog.debug("    src_scope=" + SVDBItem.getName(src_scope));
		
		if (src_scope == null || !(src_scope instanceof ISVDBNamedItem)) {
			return;
		}
		
		ISVDBNamedItem item = (ISVDBNamedItem)src_scope;
		
		if (ctxt.fLeaf.equals("") || item.getName().startsWith(ctxt.fLeaf)) {
			addProposal(new SVCompletionProposal(
					((ISVDBNamedItem)src_scope).getName(), ctxt.fStart, ctxt.fLeaf.length()));
		} else {
			findUntriggeredProposals(ctxt, src_scope);
		}
	}

	private void findUntriggeredProposals(
			SVExprContext			ctxt,
			ISVDBChildItem			src_scope) {
		fLog.debug("Looking for un-ctxt.fTriggered identifier \"" + ctxt.fLeaf + "\"");
		List<ISVDBItemBase> result = null;
		SVDBFindContentAssistNameMatcher matcher;
		
		if (ctxt.fType == ContextType.Extends) {
			// for class extension, only a class is appropriate
			matcher = new SVDBFindContentAssistNameMatcher(SVDBItemType.ClassDecl);
		} else {
			matcher = new SVDBFindContentAssistNameMatcher();
		}
		
		UntriggeredFindByNameInScopes finder_s = new UntriggeredFindByNameInScopes(
				ctxt, src_scope, getIndexIterator(), matcher);

		fLog.debug("Searching in scope hierarchy");
		result = finder_s.findItems(src_scope, ctxt.fLeaf, false);
		
		fLog.debug("    " + result.size() + " results");

		UntriggeredFindByNameInClassHierarchy finder_h =
			new UntriggeredFindByNameInClassHierarchy(ctxt, getIndexIterator(), matcher);

		// Add Class Hierarchy items
		finder_h.find(src_scope, ctxt.fLeaf);

		// Try type names
		SVDBFindNamedModIfcClassIfc finder_cls =
			new SVDBFindNamedModIfcClassIfc(getIndexIterator(), matcher);

		List<SVDBDeclCacheItem> cl_l = finder_cls.findCacheItems(ctxt.fLeaf);

		if (cl_l.size() > 0) {
			fLog.debug("Global type search for \"" + ctxt.fLeaf + 
					"\" returned " + cl_l.size());
			for (SVDBDeclCacheItem cl : cl_l) {
				fLog.debug("    " + cl.getType() + " " + cl.getName());
			}
			
			for (SVDBDeclCacheItem it : cl_l) {
				if (ctxt.fType == ContextType.Extends) {
					if (it.getType() == SVDBItemType.ClassDecl) {
						addProposal(it, ctxt.fLeaf, 0,
								SVCompletionProposal.PRIORITY_GLOBAL_SCOPE,
								true, ctxt.fStart, ctxt.fLeaf.length());
					}
				} else {
					addProposal(it, ctxt.fLeaf, 0,
							SVCompletionProposal.PRIORITY_GLOBAL_SCOPE,
							true, ctxt.fStart, ctxt.fLeaf.length());
				}
			}
		} else {
			fLog.debug("Global class find for \"" + ctxt.fLeaf + 
			"\" returned no results");
		}

		// Try global task/function/variables 
		if (ctxt.fType != ContextType.Extends) {
			SVDBFindByName finder_tf = new SVDBFindByName(getIndexIterator(), matcher);

			List<SVDBDeclCacheItem> it_l = finder_tf.findCacheItems(ctxt.fLeaf,
					SVDBItemType.Task, SVDBItemType.Function, SVDBItemType.VarDeclStmt,
					SVDBItemType.PackageDecl, SVDBItemType.TypedefStmt, SVDBItemType.VarDeclItem);

			// Remove any definitions of extern tasks/functions, 
			// since the name prefix was incorrectly matched
			for (int i=0; i<it_l.size(); i++) {
				if (it_l.get(i).getType() == SVDBItemType.Function || 
						it_l.get(i).getType() == SVDBItemType.Task) {
					// WARNING: could be time-consuming
					SVDBTask tf = (SVDBTask)it_l.get(i).getSVDBItem();
					if ((tf.getAttr() & IFieldItemAttr.FieldAttr_Extern) == 0 &&
							tf.getName().contains("::")) {
						it_l.remove(i);
						i--;
					}

					// Do not include tasks/functions unless they are completely
					// global or members of a package
					ISVDBItemBase scope_t = tf;
					while (scope_t != null && 
							scope_t.getType() != SVDBItemType.ClassDecl &&
							scope_t.getType() != SVDBItemType.ModuleDecl) {
						scope_t = ((ISVDBChildItem)scope_t).getParent();
					}

					if (scope_t != null && 
							(scope_t.getType() == SVDBItemType.ClassDecl ||
							scope_t.getType() == SVDBItemType.ModuleDecl)) {
						it_l.remove(i);
						i--;
					}
				}
			}

			if (it_l != null && it_l.size() > 0) {
				fLog.debug("Global find-by-name \"" + ctxt.fLeaf + "\" returned:");
				for (SVDBDeclCacheItem it : it_l) {
					fLog.debug("    " + it.getType() + " " + it.getName());
				}

				for (SVDBDeclCacheItem it : it_l) {
					addProposal(it, ctxt.fLeaf, 0,
							SVCompletionProposal.PRIORITY_GLOBAL_SCOPE,
							true, ctxt.fStart, ctxt.fLeaf.length());
				}
			} else {
				fLog.debug("Global find-by-name \"" + ctxt.fLeaf + 
						"\" (2) returned no results");
			}
		}
	}
	
	private boolean isSameScopeVarDecl(
			ISVDBChildItem		src_scope,
			ISVDBItemBase		proposal) {
		if (proposal instanceof SVDBVarDeclItem) {
			SVDBVarDeclItem v = (SVDBVarDeclItem)proposal;
			if (v.getParent() != null && v.getParent().getParent() != null) {
				return (v.getParent().getParent() == src_scope);
			}
		}
		return false;
	}

	private void findMacroItems(
			SVExprContext 			ctxt,
			ISVDBIndexIterator		index_it) {
//		SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
		
		if (ctxt.fRoot != null && ctxt.fRoot.equals("include")) {
			String search = ctxt.fLeaf;
			boolean str_prefix = false;
		
			// Ensure we don't include the '"' in searches
			if (search.length() > 0 && search.charAt(0) == '"') {
				search = search.substring(1);
				str_prefix = true;
			}
			
			List<SVDBIncFileInfo> inc_proposals = index_it.findIncludeFiles(
					search, ISVDBIndexIterator.FIND_INC_SV_FILES);
			
			for (SVDBIncFileInfo inc_p : inc_proposals) {
				String proposal = inc_p.getIncFile();
				
				if (ctxt.fType != ContextType.String) {
					proposal = "\"" + proposal;
				}
				proposal = proposal + "\"";
				
				SVCompletionProposal p = new SVCompletionProposal(
						proposal, ctxt.fStart, ctxt.fLeaf.length(), 
						SVCompletionProposalType.Include);
				p.setDisplayString(inc_p.getIncFile() + " (" + inc_p.getIncPath() + ")");
				p.setPriority(SVCompletionProposal.PRIORITY_PREPROC_SCOPE);
				addProposal(p);
			}
		} else {
			// most likely a macro call
			List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(new NullProgressMonitor(), 
					ctxt.fLeaf, new SVDBFindContentAssistNameMatcher(SVDBItemType.MacroDef));
			
			for (SVDBDeclCacheItem i : result) {
				fLog.debug(LEVEL_MID, "Macro: " + i.getName());
				addProposal(i.getSVDBItem(), ctxt.fLeaf, 0,
						SVCompletionProposal.PRIORITY_PREPROC_SCOPE,
						true, ctxt.fStart, ctxt.fLeaf.length());
			}
		}
	}

	private ISVDBItemBase getItemType(ISVDBItemBase item) {
		SVDBTypeInfo ti = null;
		if (item.getType() == SVDBItemType.VarDeclStmt) {
			ti = ((SVDBVarDeclStmt)item).getTypeInfo();
		} else if (item.getType() == SVDBItemType.VarDeclItem) {
			SVDBVarDeclItem vi = (SVDBVarDeclItem)item;
			if (vi.getParent() != null) {
				ti = vi.getParent().getTypeInfo();
			}
		}
		
		if (ti != null) {
			ISVDBItemBase target = resolveType(ti);
			
			if (target != null) {
				return target;
			}
		}
		
		return ti;
	}
	
	private ISVDBItemBase resolveType(SVDBTypeInfo ti) {
		ISVDBItemBase target = null;
		
		if (ti.getType() == SVDBItemType.TypeInfoUserDef) {
			SVDBFindByName finder = new SVDBFindByName(getIndexIterator());
			List<ISVDBItemBase> ret = finder.findItems(ti.getName());
			if (ret.size() > 0) {
				target = ret.get(0);
			}
		} else if (ti.getType() == SVDBItemType.TypeInfoStruct) {
			// null
		} else {
		}
		
		if (target != null) {
			if (target.getType() == SVDBItemType.TypedefStmt) {
				target = resolveType(((SVDBTypedefStmt)target).getTypeInfo());
			}
		}
		
		return target;
	}

	protected boolean isPrefix(String pre, SVDBItem it) {
		return it.getName().toLowerCase().startsWith(pre.toLowerCase());
	}

	private List<SVCompletionProposal> order_proposals(
			String										prefix, 
			Map<Integer, List<SVCompletionProposal>> 	proposals) {
		List<SVCompletionProposal> ret = new ArrayList<SVCompletionProposal>();
	
		synchronized (proposals) {
			
			for (int category=0; category <= SVCompletionProposal.PRIORITY_MAX; category++) {
				if (!proposals.containsKey(category)) {
					continue;
				}
				
		
				List<SVCompletionProposal> pl = proposals.get(category);
				
				fLog.debug("PriorityCategory " + category + " proposals");
				for (SVCompletionProposal p : pl) {
					fLog.debug("  " + p.getReplacement());
				}
				
				// First eliminate any class typedefs for which the actual class is available
				for (int i=0; i<pl.size(); i++) {
					SVCompletionProposal p = pl.get(i);
					if (p.getItemType() != null && p.getItemType().isElemOf(SVDBItemType.TypedefStmt)) {
						boolean found = false;

						for (SVCompletionProposal p_t : pl) {
							if (p_t != p && p_t.getName().equals(p.getName())) {
								found = true;
								break;
							}
						}

						if (found) {
							proposals.remove(i);
							i--;
						}
					}
				}
				
				Map<Integer, List<SVCompletionProposal>> proposal_order = new HashMap<Integer, List<SVCompletionProposal>>();
				int max_priority = -1;
				for (SVCompletionProposal p : pl) {
					if (!proposal_order.containsKey(p.getPriority())) {
						proposal_order.put(p.getPriority(), new ArrayList<SVCompletionProposal>());
					}
					if (p.getPriority() > max_priority) {
						max_priority = p.getPriority();
					}
					proposal_order.get(p.getPriority()).add(p);
				}
				
				for (int priority=0; priority <= max_priority; priority++) {
					if (proposal_order.containsKey(priority)) {
						List<SVCompletionProposal> p = proposal_order.get(priority);
						fLog.debug("Adding category " + category + " priority " + priority + " proposals");
						alphabetize(p);
						ret.addAll(p);
					}
				}
			}
		}
		
		return ret;
	}
	
	/**
	 * 
	 * @param prefix
	 * @param proposals
	 */
	private static void alphabetize(List<SVCompletionProposal> proposals) {
		for (int i = 0; i < proposals.size(); i++) {
			SVCompletionProposal p_i = proposals.get(i);
			for (int j = i + 1; j < proposals.size(); j++) {
				SVCompletionProposal p_j = proposals.get(j);
				String s_i, s_j;

				if (p_i.getItem() != null) {
					s_i = SVDBItem.getName(p_i.getItem());
				} else {
					s_i = p_i.getReplacement();
				}

				if (p_j.getItem() != null) {
					s_j = SVDBItem.getName(p_j.getItem());
				} else {
					s_j = p_j.getReplacement();
				}

				if (s_i.compareTo(s_j) > 0) {
					proposals.set(i, p_j);
					proposals.set(j, p_i);
					p_i = p_j;
				}
			}
		}
	}

	/*
	protected void addProposal(
			ISVDBItemBase 	it,
			String			prefix,
			int 			replacementOffset, 
			int 			replacementLength) {
		addProposal(it, prefix, false, replacementOffset, replacementLength);
	}
	 */

	protected void addProposal(
			SVDBDeclCacheItem 	it,
			String				prefix,
			int					priority,
			int					priority_category,
			boolean				name_based_check,
			int 				replacementOffset, 
			int 				replacementLength) {
		boolean found = false;
		
		synchronized (fCompletionProposalMap) {
			// Check if we already have it in the proposal list?
			for (int c : fCompletionProposalMap.keySet()) {
				for (SVCompletionProposal p : fCompletionProposalMap.get(c)) {
					if (p.getCacheItem() != null) {
						if (p.getCacheItem() == it) {
							found = true;
							break;
						} else if (name_based_check) {
							if (p.getName() != null && it.getName() != null) {
								if (p.getName() == it.getName()) {
									found = true;
									break;
								} else if (p.getName().equals(it.getName())) {
									found = true;
									break;
								}
							}
						}
					}
				}
				if (found) {
					break;
				}
			}

			if (!found) {
				debug("addProposal: " + it.getName() + " " + it.getType());
				SVCompletionProposal p = new SVCompletionProposal(
						it, prefix, replacementOffset, replacementLength);
				p.setPriorityCategory(priority_category);
				p.setPriority(priority);
				
				addProposal(p);
			}
		}
	}
	
	protected void addProposal(
			ISVDBItemBase 		it,
			String				prefix,
			int					priority,
			int					priority_category,
			boolean				name_based_check,
			int 				replacementOffset, 
			int 				replacementLength) {
		boolean found = false;
		
		synchronized (fCompletionProposalMap) {
			// Check if we already have it in the proposal list?
			for (int c : fCompletionProposalMap.keySet()) {
				for (SVCompletionProposal p : fCompletionProposalMap.get(c)) {
					if (p.getItem() != null) {
						if (p.getItem() == it) {
							found = true;
							break;
						} else if (name_based_check) {
							if (p.getItem() instanceof ISVDBNamedItem &&
									it instanceof ISVDBNamedItem) {
								ISVDBNamedItem i1 = (ISVDBNamedItem)p.getItem();
								ISVDBNamedItem i2 = (ISVDBNamedItem)it;
								if (i1.getName() == null || i1.getName() == null) {
									if (i1.getName() == i2.getName()) {
										found = true;
										break;
									}
								} else if (i1.getName().equals(i2.getName())) {
									found = true;
									break;
								}
							}
						}
					}
				}
				if (found) {
					break;
				}
			}

			if (!found) {
				debug("addProposal: " + SVDBItem.getName(it) + " " + it.getType());
				SVCompletionProposal p = new SVCompletionProposal(
						it, prefix, replacementOffset, replacementLength);
				p.setPriorityCategory(priority_category);
				p.setPriority(priority);
				
				addProposal(p);
			}
		}
	}
	
	protected void debug(String msg) {
		fLog.debug(msg);
	}

	private class UntriggeredFindByNameInScopes extends SVDBFindByNameInScopes {
		private SVExprContext						fCtxt;
		private ISVDBChildItem						fSrcScope;
		
		public UntriggeredFindByNameInScopes(
				SVExprContext						ctxt,
				ISVDBChildItem						src_scope,
				ISVDBIndexIterator 					index_it,
				SVDBFindContentAssistNameMatcher 	matcher) {
			super(index_it, matcher);
			fCtxt = ctxt;
			fSrcScope = src_scope;
		}

		@Override
		protected void add(ISVDBItemBase item, Scope scope, int scope_level) {
			boolean add = true;
		
			if (SVDBItem.getName(item).equals(fCtxt.fLeaf) &&
					isSameScopeVarDecl(fSrcScope, item)) {
				add = false;
			}
			
			if (add) {
				super.add(item, scope, scope_level);
				addProposal(item, fCtxt.fLeaf, scope_level,
						SVCompletionProposal.PRIORITY_BEHAVIORAL_SCOPE,
						true, fCtxt.fStart, fCtxt.fLeaf.length());
			}
		}
	}

	private class FindByNameInScopes extends SVDBFindByNameInScopes {
		private SVExprContext						fCtxt;
		
		public FindByNameInScopes(
				SVExprContext						ctxt,
				ISVDBIndexIterator 					index_it,
				SVDBFindContentAssistNameMatcher 	matcher) {
			super(index_it, matcher);
			fCtxt = ctxt;
		}

		@Override
		protected void add(ISVDBItemBase item, Scope scope, int scope_level) {
			boolean add = true;
			
			if (item.getType() == SVDBItemType.Function &&
					SVDBItem.getName(item).equals("new")) {
				add = false;
			}
			
			if (add) {
				super.add(item, scope, scope_level);		
				addProposal(item, fCtxt.fLeaf, scope_level,
						SVCompletionProposal.PRIORITY_CLS_HIERARCHY_SCOPE,
						true, fCtxt.fStart, fCtxt.fLeaf.length());
			}
		}
	}
	
	private class UntriggeredFindByNameInClassHierarchy extends SVDBFindByNameInClassHierarchy {
		private SVExprContext					fCtxt;
		
		public UntriggeredFindByNameInClassHierarchy(
				SVExprContext						ctxt,
				ISVDBIndexIterator					index_it,
				SVDBFindContentAssistNameMatcher	matcher) {
			super(index_it, matcher);
			fCtxt = ctxt;
		}

		@Override
		protected void add(ISVDBItemBase item, int scope_level) {
			boolean add = true;

			if (fCtxt.fTrigger != null && fCtxt.fTrigger.equals("=") &&
					"new".startsWith(fCtxt.fLeaf)) {
				// This is possibly a call to 'new'. We'll add
				// a proposal for this later based on the base type
				if (item.getType() == SVDBItemType.Function &&
						SVDBItem.getName(item).equals("new")) {
					add = false;
				}
			}
		
			// Filter out non-class proposals when we're dealing with
			// content-assist for a base class
			if (fCtxt.fType == ContextType.Extends) {
				fLog.debug("Extends: " + item.getType());
				if (item.getType() != SVDBItemType.ClassDecl) {
					add = false;
				}
			}
		
			// Transform any module-instance proposals to module-inst-item proposals
			if (item.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInst mi = (SVDBModIfcInst)item;
			
				// TODO:
				for (ISVDBChildItem ci : mi.getChildren()) {
					addProposal(ci, fCtxt.fLeaf, scope_level,
							SVCompletionProposal.PRIORITY_CLS_HIERARCHY_SCOPE,
							false, fCtxt.fStart, fCtxt.fLeaf.length());
				}
				add = false;
			}
			
			// TODO: Add proposal with priority
			if (add) {
				fLog.debug("Add UntriggeredClassHierarchy proposal: " +
						"scope_level=" + scope_level + " " + SVDBItem.getName(item));
				addProposal(item, fCtxt.fLeaf, scope_level,
						SVCompletionProposal.PRIORITY_CLS_HIERARCHY_SCOPE,
						true, fCtxt.fStart, fCtxt.fLeaf.length());
			}			
		}
	}
	
	private class FindByNameInClassHierarchy extends SVDBFindByNameInClassHierarchy {
		private SVExprContext						fCtxt;
		
		public FindByNameInClassHierarchy(
				SVExprContext						ctxt,
				ISVDBIndexIterator					index_it,
				SVDBFindContentAssistNameMatcher	matcher) {
			super(index_it, matcher);
			fCtxt = ctxt;
		}

		@Override
		protected void add(ISVDBItemBase item, int scope_level) {
			boolean add = true;
			
			if (item.getType() == SVDBItemType.Function &&
					SVDBItem.getName(item).equals("new")) {
				add = false;
			}
			
			if (add) {
				addProposal(item, fCtxt.fLeaf, scope_level,
						SVCompletionProposal.PRIORITY_CLS_HIERARCHY_SCOPE,
						true, fCtxt.fStart, fCtxt.fLeaf.length());
			}
		}
	}
}

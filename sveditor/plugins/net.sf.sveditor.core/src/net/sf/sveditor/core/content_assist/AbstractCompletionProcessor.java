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
import java.util.List;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModportDecl;
import net.sf.sveditor.core.db.SVDBModportItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameInClassHierarchy;
import net.sf.sveditor.core.db.search.SVDBFindByNameInScopes;
import net.sf.sveditor.core.db.search.SVDBFindContentAssistNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindIncludedFile;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVContentAssistExprVisitor;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.expr_utils.SVExprUtilsParser;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

import org.eclipse.core.runtime.NullProgressMonitor;


public abstract class AbstractCompletionProcessor implements ILogLevel {
	protected List<SVCompletionProposal>		fCompletionProposals;
	
	protected LogHandle							fLog;
	/**
	private static final String 				fBuiltInMacroProposals[] = { 
		"define", "include" 
	};
	 */
	
	public AbstractCompletionProcessor() {
		fCompletionProposals = new ArrayList<SVCompletionProposal>();
	}
	
	protected abstract ISVDBIndexIterator getIndexIterator();
	
	protected abstract SVDBFile getSVDBFile();
	
	protected void addProposal(SVCompletionProposal p) {
		boolean found = false;
	
		synchronized (fCompletionProposals) {
			for (SVCompletionProposal p_t : fCompletionProposals) {
				if (p_t.equals(p)) {
					found = true;
					break;
				}
			}

			if (!found) {
				fCompletionProposals.add(p);
			}
		}
	}
	
	public List<SVCompletionProposal> getCompletionProposals() {
		return fCompletionProposals;
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
	
		synchronized (fCompletionProposals) {
			fCompletionProposals.clear();
		}
		
		// Trigger characters and string prior to the trigger (if any)

		fLog.debug(LEVEL_MID, 
				"computeProposals: " + 
						active_file.getFilePath() + ":" + lineno + ":" + linepos);

		ISVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				active_file, lineno);
		
		if (src_scope != null) {
			fLog.debug(LEVEL_MID, "src_scope: " + src_scope.getType() + " " + SVDBItem.getName(src_scope));
		}

		/*
		if (src_scope == null) {
			debug("In global scope -- failed to find scope position @ " + lineno);
		} else {
			debug("Source scope: " + src_scope.getName());
		}
		 */

		SVExprContext ctxt = expr_scan.extractExprContext(scanner, false);
		fLog.debug(LEVEL_MID, "ctxt: trigger=" + ctxt.fTrigger + " root=" + ctxt.fRoot + 
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
						fLog.debug(LEVEL_MID, "Failed to traverse the content-assist expression");
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

		/*
		// If this is an include lookup, then use a different matching strategy
		if (ctxt.fTrigger != null && ctxt.fRoot != null &&
				ctxt.fTrigger.equals("`") && ctxt.fRoot.equals("include")) {
			expr_utils.setMatcher(new SVDBContentAssistIncludeNameMatcher());
		}
		
		List<ISVDBItemBase> items = expr_utils.findItems(
				getIndexIterator(), src_scope, ctxt, true);
		
		if (ctxt.fTrigger != null && ctxt.fTrigger.equals("`") &&
				ctxt.fRoot != null && ctxt.fRoot.startsWith("include")) {
			String replacement = "";

			for (ISVDBItemBase it : items) {
				if (!(it instanceof ISVDBNamedItem)) {
					continue;
				}
				File file = new File(((ISVDBNamedItem)it).getName());
				replacement = file.getName();
				
				// Add quotes in if not present already...
				if (!scanner.get_str(ctxt.fStart-1, 1).equals("\"")) {
					replacement = "\"" + replacement;
				}
				replacement += "\"";
				
				addProposal(new SVCompletionProposal(
						replacement, ctxt.fStart, ctxt.fLeaf.length()));
			}
		} else {
			for (ISVDBItemBase it : items) {
				addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
			}
			
			if (ctxt.fTrigger == null && !ctxt.fLeaf.trim().equals("")) {
				// Finally, add any keyword proposals
				String lc_leaf = ctxt.fLeaf.toLowerCase();
				for (String kw : SVKeywords.getKeywords()) {
					kw = kw.toLowerCase();
					if (kw.startsWith(lc_leaf)) {
						addProposal(new SVCompletionProposal(kw, ctxt.fStart, ctxt.fLeaf.length(),
								SVCompletionProposalType.Keyword));
					}
				}
			}
		}
		 */
		
		order_proposals(ctxt.fLeaf, fCompletionProposals);
	}
	
	/**
	 * findUntriggeredProposal
	 * 
	 * Find a proposal based on a request for content assist that did not start
	 * with a trigger string ( . ` ::)
	 * 
	 * These proposals are made based on the prefix string and elements from the
	 * index
	 * 
	 * @param proposals
	 * @param leaf
	private void findUntriggeredProposal(
			IBIDITextScanner			scanner,
			String 						root,
			String 						trigger,
			String 						leaf,
			int 						start) {
		ISVDBIndexIterator index_iterator = getIndexIterator();
		
		debug("findUntriggeredProposal: root=" + root + " leaf=" + leaf);

		scanner.seek(start);
		int lineno = scanner.getLocation().getLineNo();

		SVDBScopeItem src_scope = SVDBSearchUtils.findActiveScope(
				getSVDBFile(), lineno);
		
		if (src_scope == null) {
			System.out.println("[WARN] cannot locate source scope");
		}

		// Figure out which scope we're in and collect info from there...

		// Begin working outwards
		while (src_scope != null) {
			
			if (src_scope.getType() == SVDBItemType.Task || 
					src_scope.getType() == SVDBItemType.Function) {
				SVDBTaskFuncScope tf = (SVDBTaskFuncScope)src_scope;
				
				for (SVDBTaskFuncParam p : tf.getParams()) {
					if (isPrefix(leaf, p)) {
						addProposal(p, start, leaf.length());
					}
				}
			}

			// TODO: Search this scope and enclosing scopes for functions,
			// tasks, and variables
			// TODO: If one of the enclosing scopes is a class scope, then
			// search the base-class tree as well
			addMatchingTasksVars(src_scope, root, trigger, leaf, start);

			if (src_scope.getType() == SVDBItemType.Class) {
				addClassHierarchyItems(index_iterator, 
						(SVDBModIfcClassDecl)src_scope, root, trigger,
						leaf, start);
			}

			src_scope = src_scope.getParent();
		}

		for (SVDBItem it : getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function) {
				if (it.getName() != null && (leaf.equals("") 
						|| isPrefix(leaf, it))) {
					addProposal(it, start, leaf.length());
				}
			} else if (it.getType() == SVDBItemType.Module
					|| it.getType() == SVDBItemType.Class) {
				// TODO: recurse and search the scope for this
			}
		}

		// Collect all matching class names from the build path
		ISVDBItemIterator<SVDBItem> item_it = index_iterator.getItemIterator();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			if (it.getName() != null && 
					(it.getType() != SVDBItemType.File) &&
					(it.getType() != SVDBItemType.Macro) &&
					(it.getType() != SVDBItemType.Include) &&
					(leaf.equals("") || isPrefix(leaf, it))) {
				addProposal(it, start, leaf.length());
			}
		}
	}
	 */
	
	private void findTriggeredProposals(
			SVExprContext			ctxt,
			ISVDBChildItem			src_scope,
			ISVDBItemBase			leaf_item) {
		// Determine the type of the leaf item
		fLog.debug("findTriggeredProposals: " + leaf_item.getType());
		

		// Search up hierarchy ?
		if (leaf_item.getType() == SVDBItemType.ClassDecl ||
				leaf_item.getType() == SVDBItemType.TypeInfoStruct ||
				leaf_item.getType() == SVDBItemType.InterfaceDecl) {
			// Look for matching names in the target class
			SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
			SVDBFindSuperClass super_finder = new SVDBFindSuperClass(getIndexIterator()/*, matcher*/);
			ISVDBChildParent si = (ISVDBChildParent)leaf_item;
			
			while (si != null) {
				for (ISVDBChildItem it : si.getChildren()) {
					if (it.getType() == SVDBItemType.VarDeclStmt) {
						for (ISVDBItemBase it_1 : ((SVDBVarDeclStmt)it).getChildren()) {
							debug("VarDeclItem: " + SVDBItem.getName(it_1));
							if (matcher.match((ISVDBNamedItem)it_1, ctxt.fLeaf)) {
								addProposal(it_1, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
							}
						}
					} else if (it.getType() == SVDBItemType.ModportDecl) {
						for (ISVDBItemBase it_1 : ((SVDBModportDecl)it).getChildren()) {
							debug("ModportItem: " + SVDBItem.getName(it_1));
							if (matcher.match((ISVDBNamedItem)it_1, ctxt.fLeaf)) {
								addProposal(it_1, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
							}
						}
					} else if (it instanceof ISVDBNamedItem) {
						if (matcher.match((ISVDBNamedItem)it, ctxt.fLeaf)) {
							addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
						}
					}
				}
				
				if (si.getType() == SVDBItemType.ClassDecl) {
					SVDBClassDecl cls_decl = (SVDBClassDecl)si;
					si = super_finder.find(cls_decl);
				} else {
					si = null;
				}
			}
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
								addProposal(it_1, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
							}
						}
					} else if (it instanceof ISVDBNamedItem) {
						if (matcher.match((ISVDBNamedItem)it, ctxt.fLeaf)) {
							addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
						}
					}
				}
			}
		} else if (leaf_item.getType() == SVDBItemType.ModportDecl) {
			
		}
	}
	
	private void findAssignTriggeredProposals(
			SVExprContext			ctxt,
			ISVDBChildItem			src_scope,
			ISVDBItemBase			item) {
		fLog.debug("Looking for assign-triggered identifier \"" + ctxt.fLeaf + "\"");
		List<ISVDBItemBase> result = new ArrayList<ISVDBItemBase>();
		List<ISVDBItemBase> tmp = null;
		SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
		
		SVDBFindByNameInScopes finder_s = 
			new SVDBFindByNameInScopes(getIndexIterator(), matcher);
		tmp = finder_s.find(src_scope, ctxt.fLeaf, false);
		
		result.addAll(tmp);

		SVDBFindByNameInClassHierarchy finder_h =
			new SVDBFindByNameInClassHierarchy(getIndexIterator(), matcher);

		tmp = finder_h.find(src_scope, ctxt.fLeaf);
		
		result.addAll(tmp);

		if (result.size() > 0) {
			for (int i=0; i<result.size(); i++) {
				boolean add = true;
				
				if (result.get(i).getType() == SVDBItemType.Function &&
						((ISVDBNamedItem)result.get(i)).getName().equals("new")) {
					add = false;
				}
				
				if (add) {
					addProposal(result.get(i), ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
				}
			}
		}

		// Try type names
		SVDBFindNamedModIfcClassIfc finder_cls =
			new SVDBFindNamedModIfcClassIfc(getIndexIterator(), matcher);

		List<ISVDBChildItem> cl_l = finder_cls.find(ctxt.fLeaf);

		if (cl_l.size() > 0) {
			fLog.debug("Global type search for \"" + ctxt.fLeaf + 
					"\" returned " + cl_l.size());
			for (ISVDBChildItem cl : cl_l) {
				fLog.debug("    " + cl.getType() + " " + SVDBItem.getName(cl));
			}
			
			for (ISVDBItemBase it : cl_l){
				addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
			}
		} else {
			fLog.debug("Global class find for \"" + ctxt.fLeaf + 
			"\" returned no results");
		}

		// Try global task/function
		SVDBFindByName finder_tf = new SVDBFindByName(getIndexIterator(), matcher);

		/*
		List<ISVDBItemBase> it_l = finder_tf.find(ctxt.fLeaf,
				SVDBItemType.Task, SVDBItemType.Function, SVDBItemType.VarDeclStmt,
				SVDBItemType.PackageDecl);
		 */
		List<ISVDBItemBase> it_l = finder_tf.find(ctxt.fLeaf);
		
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

			for (ISVDBItemBase it : it_l) {
				addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
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
						addProposal(c, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
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
		SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
		// TODO: only provide content assist if we are in a module/interface scope
		if (src_scope == null || 
				(src_scope.getType() != SVDBItemType.ModuleDecl &&
				src_scope.getType() != SVDBItemType.InterfaceDecl)) {
			return;
		}
		// First, need to find module/interface instance in question
		SVDBModIfcInst inst = findInst(src_scope, lineno, linepos);
		
		if (inst == null) {
			fLog.debug("failed to find target module/interface instantiation");
			return;
		}
		
		fLog.debug("instance type: " + inst.getTypeName());
		
		SVDBModIfcDecl decl;
		SVDBFindNamedModIfcClassIfc finder = new SVDBFindNamedModIfcClassIfc(getIndexIterator());
		List<ISVDBChildItem> result = finder.find(inst.getTypeName());
		
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
					addProposal(pi, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
				}
			}
		}
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
				if (c.getLocation().getLine() > lineno) {
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
		SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
		SVDBFindByNameInScopes finder_s =
			new SVDBFindByNameInScopes(getIndexIterator(), matcher);

		fLog.debug("Searching in scope hierarchy");
		result = finder_s.find(src_scope, ctxt.fLeaf, false);
		
		fLog.debug("    " + result.size() + " results");
		for (int i=0; i<result.size(); i++) {
			// It's possible that the local variable that we're declaring
			// will appear in the proposals. Don't add these proposals. 
			if (!(SVDBItem.getName(result.get(i)).equals(ctxt.fLeaf) &&
					isSameScopeVarDecl(src_scope, result.get(i)))) {
				addProposal(result.get(i), ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
			}
		}

		SVDBFindByNameInClassHierarchy finder_h =
			new SVDBFindByNameInClassHierarchy(getIndexIterator(), matcher);

		result = finder_h.find(src_scope, ctxt.fLeaf);

		if (result.size() > 0) {
			for (int i=0; i<result.size(); i++) {
				boolean add = true;
				
				if (ctxt.fTrigger != null && ctxt.fTrigger.equals("=") &&
						"new".startsWith(ctxt.fLeaf)) {
					// This is possibly a call to 'new'. We'll add
					// a proposal for this later based on the base type
					if (result.get(i).getType() == SVDBItemType.Function &&
							((ISVDBNamedItem)result.get(i)).getName().equals("new")) {
						add = false;
					}
				}
				
				if (add) {
					addProposal(result.get(i), ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
				}
			}
		}

		// Try type names
		SVDBFindNamedModIfcClassIfc finder_cls =
			new SVDBFindNamedModIfcClassIfc(getIndexIterator(), matcher);

		List<ISVDBChildItem> cl_l = finder_cls.find(ctxt.fLeaf);

		if (cl_l.size() > 0) {
			fLog.debug("Global type search for \"" + ctxt.fLeaf + 
					"\" returned " + cl_l.size());
			for (ISVDBChildItem cl : cl_l) {
				fLog.debug("    " + cl.getType() + " " + SVDBItem.getName(cl));
			}
			
			for (ISVDBItemBase it : cl_l){
				addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
			}
		} else {
			fLog.debug("Global class find for \"" + ctxt.fLeaf + 
			"\" returned no results");
		}

		// Try global task/function
		SVDBFindByName finder_tf = new SVDBFindByName(getIndexIterator(), matcher);

		List<ISVDBItemBase> it_l = finder_tf.find(ctxt.fLeaf,
				SVDBItemType.Task, SVDBItemType.Function, SVDBItemType.VarDeclStmt,
				SVDBItemType.PackageDecl, SVDBItemType.TypedefStmt);
		/*
		List<ISVDBItemBase> it_l = finder_tf.find(ctxt.fLeaf);
		 */
		
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

			for (ISVDBItemBase it : it_l) {
				addProposal(it, ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
			}
		} else {
			fLog.debug("Global find-by-name \"" + ctxt.fLeaf + 
			"\" (2) returned no results");
		}
		
		// Special case: If this is a constructor call, then do a 
		// context lookup on the LHS
		/*
		if (root != null && ctxt.fTrigger != null && ctxt.fTrigger.equals("=") &&
				ctxt.fLeaf != null && "new".startsWith(ctxt.fLeaf)) {
			fLog.debug("Looking for new in root=" + root);
			findctxt.fTriggeredItems(root, "=", "new", src_scope, 
					getIndexIterator(), max_matches, false, ret);
		}
		 */
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
		SVDBFindContentAssistNameMatcher matcher = new SVDBFindContentAssistNameMatcher();
		
		if (ctxt.fRoot != null && ctxt.fRoot.equals("include")) {
			SVDBFindIncludedFile finder = new SVDBFindIncludedFile(
					index_it, matcher);
			List<SVDBFile> it_l = finder.find(ctxt.fLeaf);

			if (it_l.size() > 0) {
				addProposal(it_l.get(0), ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
			}
		} else {
			// most likely a macro call
			List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(new NullProgressMonitor(), 
					ctxt.fLeaf, new SVDBFindContentAssistNameMatcher(SVDBItemType.MacroDef));
			
			for (SVDBDeclCacheItem i : result) {
				fLog.debug(LEVEL_MID, "Macro: " + i.getName());
				addProposal(i.getSVDBItem(), ctxt.fLeaf, ctxt.fStart, ctxt.fLeaf.length());
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
			List<ISVDBItemBase> ret = finder.find(ti.getName());
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

	/**
	 * Find proposals that result from a triggered content-assist request
	 * 
	 * Typical strings will be something like: a.b<request>
	 * 
	 * @param viewer
	 * @param src_scope
	 * @param pre_trigger_idx
	 * @param trigger
	 * @param leaf
	 * @param start
	 * @param proposals
	private void findTriggeredProposals(
			IBIDITextScanner	scanner,
			SVDBScopeItem		src_scope,
			String				root,
			String				trigger,
			String				leaf,
			int					start) {
		ISVDBIndexIterator index_iterator = getIndexIterator();
		SVExpressionUtils expr_utils = new SVExpressionUtils();
		
		debug("findTriggeredProposals: " + src_scope.getName() + 
				" pre=" + leaf + " trigger=" + trigger);
		
		debug("    preTrigger=" + leaf);
		List<SVDBItem> info = expr_utils.processPreTriggerPortion(
				index_iterator, src_scope, root, true);
		
		final List<SVDBItem> result_f = new ArrayList<SVDBItem>();
		
		if (info != null && info.size() > 0) {
			// Get the last item
			SVDBItem res = info.get(info.size()-1);
			final String pre_f = leaf;
			
			debug("use " + res.getName());
			
			SVDBModIfcClassDecl res_c = (SVDBModIfcClassDecl)res;
			SVDBFindSuperClass finder_sc = new SVDBFindSuperClass(index_iterator);

			while (res_c != null) {
				
				for (SVDBItem it : res_c.getItems()) {
					if (isPrefix(pre_f, it)) {
						result_f.add(it);
					}
				}

				if (res_c.getSuperClass() != null) {
					res_c = finder_sc.find(res_c);
				} else {
					res_c = null;
				}
			}
		}
		
		for (SVDBItem it : result_f) {
			addProposal(it, start, leaf.length());
		}
	}
	 */

	/**
	private void addMatchingTasksVars(
			SVDBScopeItem 	src_scope, 
			String 			root, 
			String 			trigger, 
			String 			pre, 
			int 			start) {
		debug("addMatchingTasksVars: " + src_scope.getName() + " pre=" + pre);

		for (SVDBItem it : src_scope.getItems()) {
			debug("    it=" + it.getName() + " type=" +	it.getType());
			if (it.getType() == SVDBItemType.Task
					|| it.getType() == SVDBItemType.Function
					|| it.getType() == SVDBItemType.VarDecl
					|| it.getType() == SVDBItemType.TaskFuncParam) {
				if (isPrefix(pre, it)) {
					addProposal(it, start, pre.length());
				}
			}
		}
	}
	 */
	
	/**
	private void addMacroProposals(
			String							pre,
			SVDBScopeItem					scope,
			int								replacementOffset) {
		
		for (SVDBItem it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Macro) {
				if (it.getName() != null && 
						(pre.equals("") || isPrefix(pre, it))) {
					addProposal(it, replacementOffset, pre.length());
				}
			} else if (it instanceof ISVDBScopeItem) {
				addMacroProposals(
						pre, (ISVDBScopeItem)it, replacementOffset);
			}
		}
	}
	 */


	/**
	 * Traverse the class hierarchy and add tasks, functions, and members to the
	 * completion proposals
	 * 
	 * @param searcher
	 * @param src_scope
	 * @param doc
	 * @param root
	 * @param trigger
	 * @param pre
	 * @param start
	 * @param proposals
	private void addClassHierarchyItems(
			ISVDBIndexIterator			index_it,
			SVDBModIfcClassDecl 		src_scope, 
			String 						root,
			String 						trigger, 
			String 						pre, 
			int 						start) {
		debug("addClassHierarchyItems()");

		while (true) {
			debug("src_scope=" + src_scope.getName()
					+ " superClass=" + src_scope.getSuperClass());
			SVDBModIfcClassDecl src_scope_t = src_scope;
			SVDBFindNamedModIfcClassIfc finder_class =
				new SVDBFindNamedModIfcClassIfc(index_it);
			
			if (src_scope.getSuperClass() == null
					|| (src_scope = finder_class.find(
							src_scope.getSuperClass())) == null) {
				debug("End expansion: " + src_scope_t.getName());
				debug("    SuperClass="	+ src_scope_t.getSuperClass());
				debug("    Find="
						+ finder_class.find(src_scope_t.getSuperClass()));
				break;
			}

			addMatchingTasksVars(src_scope, root, trigger, pre, start);
		}
	}
	 */

	/**
	 * findPreProcProposals()
	 * 
	 * Find macro completion proposals
	 * 
	 * @param proposals
	 * @param pre
	private void findPreProcProposals(
			IBIDITextScanner			scanner,
			String 						root, 
			String 						trigger, 
			String 						pre,
			int 						start) {
		ISVDBIndexIterator index_it = getIndexIterator();

		if (pre.startsWith("include")) {
			boolean leading_quote = false, trailing_quote = false;
			String replacement = "";

			// Look at the point beyond the '`include'
			String post_include = pre.substring("include".length());

			start += "include".length();

			// Now, account for any whitespace
			while (post_include.length() > 0
					&& Character.isWhitespace(post_include.charAt(0))) {
				post_include = post_include.substring(1);
				start++;
			}

			if (post_include.startsWith("\"")) {
				// strip away the quote
				leading_quote = true;
				post_include = post_include.substring(1);
				start++;
			}

			// look for include files that match the user-specified pattern
			
			// Collect all matching class names from the build path
			ISVDBItemIterator<SVDBItem> item_it = index_it.getItemIterator();
			
			while (item_it.hasNext()) {
				SVDBItem it = item_it.nextItem();
				
				if (it.getType() != SVDBItemType.Include) {
					continue;
				}
				
				File file = new File(it.getName());
				
				if (file.getName().toLowerCase().startsWith(post_include.toLowerCase())) {
					replacement = file.getName();

					// Add quotes in if not present already...
					if (!leading_quote) {
						replacement = "\"" + replacement;
					}
					if (!trailing_quote) {
						replacement += "\"";
					}

					int replacement_length = post_include.length();
					// replacementString
					// replacementOffset
					// replacementLength
					// cursorPosition
					addProposal(new SVCompletionProposal(replacement,
							start, replacement_length));
				}
			}
		} else {
			for (String p : fBuiltInMacroProposals) {
				if (p.toLowerCase().startsWith(pre.toLowerCase())) {
					addProposal(new SVCompletionProposal(p, start, pre.length()));
				}
			}
			ISVDBItemIterator<SVDBItem> item_it = index_it.getItemIterator();
			
			while (item_it.hasNext()) {
				SVDBItem it = item_it.nextItem();
				
				if (it.getType() == SVDBItemType.Macro &&
						isPrefix(pre, it)) {
					addProposal(it, start, pre.length());
				}
				debug("it=" + it.getName());
			}
		}
	}
	 */


	protected boolean isPrefix(String pre, SVDBItem it) {
		return it.getName().toLowerCase().startsWith(pre.toLowerCase());
	}

	/**
	 * order_proposals()
	 * 
	 * Re-order the proposals to be in alphabetical order
	 * 
	 * @param proposals
	 */
	private void order_proposals(String prefix, List<SVCompletionProposal> proposals) {
	
		synchronized (proposals) {
			// First eliminate any class typedefs for which the actual class is available
			for (int i=0; i<proposals.size(); i++) {
				SVCompletionProposal p = proposals.get(i);
				if (p.getItem() != null && SVDBStmt.isType(p.getItem(), SVDBItemType.TypedefStmt)) {
					boolean found = false;

					for (SVCompletionProposal p_t : proposals) {
						if (p_t != p && p_t.getItem() != null && 
								SVDBItem.getName(p_t.getItem()).equals(SVDBItem.getName(p.getItem()))) {
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

			for (int i=0; i<proposals.size(); i++) {
				SVCompletionProposal p_i = proposals.get(i);
				for (int j=i+1; j<proposals.size(); j++) {
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

					if (prefix.compareTo(s_i) < prefix.compareTo(s_j)) {
						proposals.set(i, p_j);
						proposals.set(j, p_i);
						p_i = p_j;
					}
				}
			}
		}
	}

	protected void addProposal(
			ISVDBItemBase 	it,
			String			prefix,
			int 			replacementOffset, 
			int 			replacementLength) {
		boolean found = false;

		synchronized (fCompletionProposals) {
			// Check if we already have it in the proposal list?
			for (SVCompletionProposal p : fCompletionProposals) {
				if (p.getItem() != null && p.getItem() == it) {
					found = true;
					break;
				}
			}

			if (!found) {
				debug("addProposal: " + SVDBItem.getName(it) + " " + it.getType());
				addProposal(new SVCompletionProposal(it, prefix, 
						replacementOffset, replacementLength));
			}
		}
	}
	
	protected void debug(String msg) {
		fLog.debug(msg);
	}

}

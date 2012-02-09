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


package net.sf.sveditor.ui.svcp;

import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBInitialStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

public class SVDBDefaultContentFilter extends ViewerFilter {
	////////////////////////////////////////////////////////////////////////////////////////////////
	// By default hide 
	////////////////////////////////////////////////////////////////////////////////////////////////
	// - assign statements
	// - always blocks 
	// - initial blocks
	// - generate blocks
	private boolean hide_assign_statements		= true;
	private boolean hide_always_statements		= true;
	private boolean hide_initial_blocks  		= true;
	private boolean hide_generate_blocks 		= true;
	////////////////////////////////////////////////////////////////////////////////////////////////
	// By default show:
	////////////////////////////////////////////////////////////////////////////////////////////////
	// - variable declarations
	private boolean hide_variable_declarations  = false;
	// task & function declarations
	private boolean hide_task_functions 		= false;
	// - module instances 
	private boolean hide_module_instances		= false;
	// - include flies
	//   + regular include files
	//   + import files
	private boolean hide_include_files      	= false;
	
	

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		
		if (element instanceof SVDBItem &&
						(((SVDBItem)element).getType() == SVDBItemType.Marker)
			     ) {
			return false;
		}
		
		// Variable declarations
		// These include 
		// normal variable declarations (wire, logic etc)
		// genvars
		else if ((hide_variable_declarations == true) && (
					(element instanceof SVDBVarDeclItem)) 
				){
			return false;
		}

		// Assign declarations
		else if ((hide_assign_statements == true) && (element instanceof SVDBAssign))  {
			return false;
		}

		// Always declarations
		else if ((hide_always_statements == true) && (element instanceof SVDBAlwaysStmt))  {
			return false;
		}

		// Generate blocks
		else if ((hide_generate_blocks == true) && (element instanceof SVDBGenerateBlock))  {
			return false;
		}
		
		// Module interface instance declarations
		else if ((hide_module_instances == true) && (element instanceof SVDBModIfcInstItem))  {
			return false;
		}
		
		// Module initial declarations
		else if ((hide_initial_blocks == true) && (element instanceof SVDBInitialStmt))  {
			return false;
		}
		
		// task / function initial declarations
		else if ((hide_task_functions == true) && 
					(
							// TODO: is SVDBFunction used anywhere??? Functions seem to be part of the tasks group
//						(element instanceof SVDBFunction) ||
						(element instanceof SVDBTask)
					)
				)  {
			return false;
		}
		
		// Module include declarations
		// Module import declarations
		else if ((hide_include_files == true) && 
					(
						(element instanceof SVDBInclude) ||		// include files 
						(element instanceof SVDBImportItem)		// import statements
					)
				)  {
			return false;		}
		
		return true;
	}

	/**
	 * Toggle whether tasks & function declarations are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleTaskFunctions  ()  {
		hide_task_functions = !hide_task_functions;
		return (hide_task_functions);
	}
	
	/**
	 * Toggle whether variables are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleVariableDeclarations ()  {
		hide_variable_declarations  = !hide_variable_declarations;
		return (hide_variable_declarations);
	}

	/**
	 * Toggle whether assign statements are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleAssignStatements ()  {
		hide_assign_statements  = !hide_assign_statements;
		return (hide_assign_statements);
	}

	/**
	 * Toggle whether always statements are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleAlwaysStatements ()  {
		hide_always_statements = !hide_always_statements;
		return (hide_always_statements);
	}

	/**
	 * Toggle whether generate blocks are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleGenerateBlocks ()  {
		hide_generate_blocks = !hide_generate_blocks;
		return (hide_generate_blocks);
	}
	
	/**
	 * Toggle whether module instances are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleModuleInstances ()  {
		hide_module_instances = !hide_module_instances;
		return (hide_module_instances);
	}

	/**
	 * Toggle whether initial blocks are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleInitialBlocks ()  {
		hide_initial_blocks = !hide_initial_blocks;
		return (hide_initial_blocks);
	}

	/**
	 * Toggle whether include files are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleIncludeFiles ()  {
		hide_include_files = !hide_include_files;
		return (hide_include_files);
	}

	/**
	 * Toggle whether tasks & function declarations are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideTaskFunctions  (boolean hide)  {
		hide_task_functions = hide;
	}
	
	/**
	 * Toggle whether variables are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideVariableDeclarations (boolean hide)  {
		hide_variable_declarations  = hide;
	}
	
	/**
	 * Toggle whether assign statements are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideAssignStatements (boolean hide)  {
		hide_assign_statements  = hide;
	}
	
	/**
	 * Toggle whether always statements are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideAlwaysStatements (boolean hide)  {
		hide_always_statements = hide;
	}
	
	/**
	 * Toggle whether generate blocks are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideGenerateBlocks (boolean hide)  {
		hide_generate_blocks = hide;
	}
	
	/**
	 * Toggle whether module instances are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideModuleInstances (boolean hide)  {
		hide_module_instances = hide;
	}
	
	/**
	 * Toggle whether initial blocks are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideInitialBlocks (boolean hide)  {
		hide_initial_blocks = hide;
	}
	
	/**
	 * Toggle whether include files are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideIncludeFiles (boolean hide)  {
		hide_include_files = hide;
	}
	
}

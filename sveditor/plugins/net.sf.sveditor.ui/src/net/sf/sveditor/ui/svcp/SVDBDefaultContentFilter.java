/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBCoverpoint;
import net.sf.sveditor.core.db.SVDBCoverpointBins;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
import net.sf.sveditor.core.db.SVDBGenerateIf;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBProperty;
import net.sf.sveditor.core.db.SVDBSequence;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssertStmt;
import net.sf.sveditor.core.db.stmt.SVDBBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBCoverStmt;
import net.sf.sveditor.core.db.stmt.SVDBDefParamItem;
import net.sf.sveditor.core.db.stmt.SVDBExprStmt;
import net.sf.sveditor.core.db.stmt.SVDBFinalStmt;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBInitialStmt;
import net.sf.sveditor.core.db.stmt.SVDBTimePrecisionStmt;
import net.sf.sveditor.core.db.stmt.SVDBTimeUnitsStmt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
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
	private boolean hide_define_statements		= true;
	private boolean hide_variable_declarations	= true;	// - variable declarations
	private boolean hide_constraints			= true;	// - Constraints
	private boolean hide_enum_typedefs			= true;	// - Enumerated types & typedefs
	private boolean hide_assertion_properties	= true;	// - Assertion Property & Sequence
	private boolean hide_cover_point_group_cross= true;	// - Cover Group, Point & Cross Coverage
	////////////////////////////////////////////////////////////////////////////////////////////////
	// By default show:
	////////////////////////////////////////////////////////////////////////////////////////////////
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
					(element instanceof SVDBVarDeclItem) ||
					// For some reason Parameters are type of SVDBVarDecItem, so going to include defparams here
					// to keep things consistent.
					// Parameters should probably fall under 'defines though
					(element instanceof SVDBDefParamItem))		
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
		else if ((hide_generate_blocks == true) && ((element instanceof SVDBGenerateBlock) || (element instanceof SVDBGenerateIf)))  {
			return false;
		}
		
		// Module interface instance declarations
		else if ((hide_module_instances == true) && (element instanceof SVDBModIfcInstItem))  {
			return false;
		}
		
		// Module initial declarations
		else if ((hide_initial_blocks == true) && ((element instanceof SVDBInitialStmt) || (element instanceof SVDBFinalStmt)))  {
			return false;
		}
		
		// Module initial declarations
		else if ((hide_define_statements == true) && (element instanceof SVDBMacroDef))  {
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
		
		// Assertion, Property, Sequence declarations
		else if ((hide_assertion_properties == true) && 
					(
						(element instanceof SVDBSequence) || 
						(element instanceof SVDBProperty) || 
						(element instanceof SVDBAssertStmt) 
					)
				){
			return false;
		}
		
		// Cover Point, Group Cross declarations
		else if ((hide_cover_point_group_cross== true) && 
				(
						(element instanceof SVDBCoverpoint) || 
						(element instanceof SVDBCovergroup) || 
						(element instanceof SVDBCoverStmt) || 
						(element instanceof SVDBCoverpointCross) ||
						(element instanceof SVDBCoverpointBins)
						)
				){
			return false;
		}
		
		// Enumerated Types / Typedef declarations
		else if ((hide_enum_typedefs == true) && 
				(
						(element instanceof SVDBTypedefStmt) || 
						(element instanceof SVDBTypeInfoEnum)		// TODO Is this what we need for enums? 
						)
				){
			return false;
		}
		
		// constraints initial declarations
		else if ((hide_constraints == true) && (element instanceof SVDBConstraint))  {
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
		
		// This section contains miscellaneous stuff in the DB, that we don't want displayed
		else if (
					(element instanceof SVDBExprStmt) || // Statements in a property 
					(element instanceof SVDBTimePrecisionStmt) || // timeprecision 
					(element instanceof SVDBTimeUnitsStmt) || // timeunits 
					(element instanceof SVDBBlockStmt) // Begin / end pairs - always hide 
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
	 * Toggle whether tasks & function declarations are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleConstraints  ()  {
		hide_constraints = !hide_constraints;
		return (hide_constraints);
	}
	
	/**
	 * Toggle whether assertions, sequences and properties declarations are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleAssertionProperties  ()  {
		hide_assertion_properties = !hide_assertion_properties;
		return (hide_assertion_properties);
	}
	
	/**
	 * Toggle whether Cover Point, Group or Cross declarations are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleCoverPointGroupCross ()  {
		hide_cover_point_group_cross = !hide_cover_point_group_cross;
		return (hide_cover_point_group_cross);
	}
	
	/**
	 * Toggle whether assertions, sequences and properties declarations are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleEnumTypedefs  ()  {
		hide_enum_typedefs = !hide_enum_typedefs;
		return (hide_enum_typedefs);
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
	 * Toggle whether `defines are shown or not
	 * @param: None
	 * @return: True if enabled, false if not
	 */
	public boolean ToggleDefineStatements ()  {
		hide_define_statements = !hide_define_statements;
		return (hide_define_statements);
	}
	
	/**
	 * Set whether tasks & function declarations are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideTaskFunctions  (boolean hide)  {
		hide_task_functions = hide;
	}
	
	/**
	 * Set whether Constraint declarations are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideConstraints  (boolean hide)  {
		hide_constraints = hide;
	}
	
	/**
	 * Set whether Assertion Property and Sequence declarations are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideAssertionProperties  (boolean hide)  {
		hide_assertion_properties = hide;
	}
	
	/**
	 * Set whether Cover Point, Group and Cross declarations are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideCoverPointGroupCross  (boolean hide)  {
		hide_cover_point_group_cross = hide;
	}
	
	/**
	 * Set whether Enumerated types / typedef declarations are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideEnumTypedefs (boolean hide)  {
		hide_enum_typedefs = hide;
	}
	
	/**
	 * Set whether variables are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideVariableDeclarations (boolean hide)  {
		hide_variable_declarations  = hide;
	}
	
	/**
	 * Set whether assign statements are shown or not
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
	 * Set whether module instances are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideModuleInstances (boolean hide)  {
		hide_module_instances = hide;
	}
	
	/**
	 * Set whether initial blocks are shown or not
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

	/**
	 * Set whether `defines are shown or not
	 * @param: hide - true - hide element, false show element
	 */
	public void HideDefineStatements (boolean hide)  {
		hide_define_statements = hide;
	}
	
}

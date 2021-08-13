/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.sveditor.ui;

public interface ISVIcons {
	
	String OBJ_ICONS = "icons/edecl16/";
	String FILE_OBJ = "icons/vlog_16_16.gif";
	String FOLDER_OBJ = "icons/eview16/folder.gif";
	String H_FOLDER_OBJ = "icons/eview16/hfolder_obj.gif";
	String SV_LIB = "icons/eview16/sv_lib.gif";
	
	String MODULE_OBJ = OBJ_ICONS + "module_obj.gif";
	String PROGRAM_OBJ = OBJ_ICONS + "program_obj.gif";
	String CONFIG_OBJ = OBJ_ICONS + "config_obj.gif";
	String INTERFACE_OBJ = OBJ_ICONS + "int_obj.gif";
	String MODPORT_OBJ = OBJ_ICONS + "modport_obj.gif";
	String CLASS_OBJ = OBJ_ICONS + "class_obj.gif";
	String DEFINE_OBJ = OBJ_ICONS + "define_obj.gif";
	String INCLUDE_OBJ = OBJ_ICONS + "include_obj.gif";
	String PACKAGE_OBJ = OBJ_ICONS + "package.gif";
	String STRUCT_OBJ = OBJ_ICONS + "struct_obj.gif";
	String COVERGROUP_OBJ = OBJ_ICONS + "covergroup_16_16.gif";
	String COVERPOINT_OBJ = OBJ_ICONS + "coverpoint_16_16.gif";
	String COVERPOINT_CROSS_OBJ = OBJ_ICONS + "coverpoint_cross_16_16.gif";
	String SEQUENCE_OBJ = OBJ_ICONS + "sequence_16_16.gif";
	String ASSERT_OBJ = OBJ_ICONS + "property_16_16.gif";		// TODO Create an ICON for assertions
	String PROPERTY_OBJ  = OBJ_ICONS + "property_16_16.gif";
	String MOD_IFC_INST_OBJ = OBJ_ICONS + "mod_ifc_inst.gif";
	String LOCAL_OBJ        = OBJ_ICONS + "localvariable_obj.gif";
	String ENUM_TYPE_OBJ = OBJ_ICONS + "enum_obj.gif";
	String TYPEDEF_TYPE_OBJ = OBJ_ICONS + "typedef_obj.gif";

	String DECL_ICONS = "icons/edecl16/";
	String FIELD_PRIV_OBJ = DECL_ICONS + "field_private_obj.gif";
	String FIELD_PROT_OBJ = DECL_ICONS + "field_protected_obj.gif";
	String FIELD_PUB_OBJ = DECL_ICONS + "field_public_obj.gif";
	
	String CONSTRAINT_OBJ = OBJ_ICONS + "constraint_obj.gif";
	String ALWAYS_BLOCK_OBJ = OBJ_ICONS + "always_obj.gif";
	String INITIAL_OBJ = OBJ_ICONS + "initial_obj.gif";
	String ASSIGN_OBJ  = OBJ_ICONS + "assign_obj.gif";
	String GENERATE_OBJ = OBJ_ICONS + "generate_obj.gif";
	String CLOCKING_OBJ = OBJ_ICONS + "clocking_16_16.gif";

	String TASK_PRIV_OBJ = DECL_ICONS + "private_co.gif";
	String TASK_PROT_OBJ = DECL_ICONS + "protected_co.gif";
	String TASK_PUB_OBJ = DECL_ICONS + "public_co.gif";
	String IMPORT_OBJ = DECL_ICONS + "impc_obj.gif";
	
	String VIEW_ICONS = "icons/eview16/";
	String ARGFILE = VIEW_ICONS + "configs.gif";
	
}

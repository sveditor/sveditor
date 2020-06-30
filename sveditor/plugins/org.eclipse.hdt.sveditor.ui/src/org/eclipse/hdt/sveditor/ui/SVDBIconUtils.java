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


package org.eclipse.hdt.sveditor.ui;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.db.IFieldItemAttr;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBTypedefStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;

public class SVDBIconUtils implements ISVIcons {
	
	private static final Map<SVDBItemType, String>		fImgDescMap;
	
	static {
		fImgDescMap = new HashMap<SVDBItemType, String>();

		fImgDescMap.put(SVDBItemType.File, FILE_OBJ);
		fImgDescMap.put(SVDBItemType.ModuleDecl, MODULE_OBJ);
		fImgDescMap.put(SVDBItemType.ProgramDecl, PROGRAM_OBJ);
		fImgDescMap.put(SVDBItemType.InterfaceDecl, INTERFACE_OBJ);
		fImgDescMap.put(SVDBItemType.ModportDecl, MODPORT_OBJ);
		fImgDescMap.put(SVDBItemType.ModportItem, MODPORT_OBJ);
		fImgDescMap.put(SVDBItemType.ConfigDecl, CONFIG_OBJ);
		fImgDescMap.put(SVDBItemType.ClassDecl, CLASS_OBJ);
		fImgDescMap.put(SVDBItemType.MacroDef, DEFINE_OBJ);
		fImgDescMap.put(SVDBItemType.DefParamItem, FIELD_PUB_OBJ);
		fImgDescMap.put(SVDBItemType.Include, INCLUDE_OBJ);
		fImgDescMap.put(SVDBItemType.PackageDecl, PACKAGE_OBJ);
		fImgDescMap.put(SVDBItemType.TypeInfoStruct, STRUCT_OBJ);
		fImgDescMap.put(SVDBItemType.Covergroup, COVERGROUP_OBJ);
		fImgDescMap.put(SVDBItemType.Coverpoint, COVERPOINT_OBJ);
		fImgDescMap.put(SVDBItemType.CoverStmt, COVERPOINT_OBJ);
		fImgDescMap.put(SVDBItemType.CoverpointCross, COVERPOINT_CROSS_OBJ);
		fImgDescMap.put(SVDBItemType.Sequence, SEQUENCE_OBJ);
		fImgDescMap.put(SVDBItemType.Property, PROPERTY_OBJ);
		fImgDescMap.put(SVDBItemType.AssertStmt, ASSERT_OBJ);
		fImgDescMap.put(SVDBItemType.Constraint, CONSTRAINT_OBJ);
		fImgDescMap.put(SVDBItemType.AlwaysStmt, ALWAYS_BLOCK_OBJ);
		fImgDescMap.put(SVDBItemType.InitialStmt, INITIAL_OBJ);
		fImgDescMap.put(SVDBItemType.FinalStmt, INITIAL_OBJ);
		fImgDescMap.put(SVDBItemType.Assign, ASSIGN_OBJ);
		fImgDescMap.put(SVDBItemType.GenerateBlock, GENERATE_OBJ);
		fImgDescMap.put(SVDBItemType.GenerateIf, GENERATE_OBJ);
		fImgDescMap.put(SVDBItemType.GenerateFor, GENERATE_OBJ);
		fImgDescMap.put(SVDBItemType.ClockingBlock, CLOCKING_OBJ);
		fImgDescMap.put(SVDBItemType.ImportItem, IMPORT_OBJ);
		fImgDescMap.put(SVDBItemType.ModIfcInst, MOD_IFC_INST_OBJ);
		fImgDescMap.put(SVDBItemType.ModIfcInstItem, MOD_IFC_INST_OBJ);
		fImgDescMap.put(SVDBItemType.VarDeclItem, FIELD_PUB_OBJ);
		fImgDescMap.put(SVDBItemType.Task, TASK_PUB_OBJ);
		fImgDescMap.put(SVDBItemType.TypedefStmt, ENUM_TYPE_OBJ);
		
		fImgDescMap.put(SVDBItemType.ArgFileIncDirStmt, H_FOLDER_OBJ);
		fImgDescMap.put(SVDBItemType.ArgFilePathStmt, FILE_OBJ);
		fImgDescMap.put(SVDBItemType.ArgFileDefineStmt, DEFINE_OBJ);
		fImgDescMap.put(SVDBItemType.ArgFileIncFileStmt, ARGFILE);
		fImgDescMap.put(SVDBItemType.ArgFileSrcLibPathStmt, SV_LIB);

	}
	
	public static Image getIcon(String key) {
		return SVUiPlugin.getImage(key);
	}
	
	public static Image getIcon(SVDBItemType type) {
		if (fImgDescMap.containsKey(type))  {
			return SVUiPlugin.getImage(fImgDescMap.get(type)); 
		}
		return null;
	}
	
	public static Image getIcon(ISVDBItemBase it) {
		if (it.getType() == SVDBItemType.VarDeclItem) {
			SVDBVarDeclItem decl = (SVDBVarDeclItem)it;
			SVDBVarDeclStmt decl_p = decl.getParent();
			
			if (decl_p == null) {
				System.out.println("Parent of " + decl.getName() + " @ " + 
						SVDBLocation.unpackLineno(decl.getLocation()) + " is NULL");
			}
			int attr = decl_p.getAttr();
			if (decl_p.getParent() != null && 
					(decl_p.getParent().getType() == SVDBItemType.Task ||
							decl_p.getParent().getType() == SVDBItemType.Function)) {
				return SVUiPlugin.getImage(LOCAL_OBJ);
			} else {
				if ((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
					return SVUiPlugin.getImage(FIELD_PRIV_OBJ);
				} else if ((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
					return SVUiPlugin.getImage(FIELD_PROT_OBJ);
				} else {
					return SVUiPlugin.getImage(FIELD_PUB_OBJ);
				}
			}
		} else if (it instanceof IFieldItemAttr) {
			int            attr = ((IFieldItemAttr)it).getAttr();
			SVDBItemType   type = it.getType();
			
			if (type == SVDBItemType.ModIfcInstItem) {
				return SVUiPlugin.getImage(MOD_IFC_INST_OBJ);
			} else if (type == SVDBItemType.Task || 
					type == SVDBItemType.Function) {
				if ((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
					return SVUiPlugin.getImage(TASK_PRIV_OBJ);
				} else if ((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
					return SVUiPlugin.getImage(TASK_PROT_OBJ);
				} else {
					return SVUiPlugin.getImage(TASK_PUB_OBJ);
				}
			} else if (SVDBStmt.isType(it, SVDBItemType.ParamPortDecl)) {
				return SVUiPlugin.getImage(LOCAL_OBJ);
			}
		} else if (it instanceof ISVDBItemBase) {
			SVDBItemType type = ((ISVDBItemBase)it).getType();
			
			if (fImgDescMap.containsKey(type)) {
				return SVUiPlugin.getImage(fImgDescMap.get(type));
			} else if (it.getType() == SVDBItemType.TypedefStmt) {
				SVDBTypedefStmt td = (SVDBTypedefStmt)it;
				
				if (td.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
					return SVUiPlugin.getImage(ENUM_TYPE_OBJ);
				} else {
					return SVUiPlugin.getImage(TYPEDEF_TYPE_OBJ);
				}
			}
		}
		
		return null;
	}
	
    public static ImageDescriptor getImageDescriptor(SVDBItemType it) {
		if (fImgDescMap.containsKey(it))  {
			return SVUiPlugin.getImageDescriptor(fImgDescMap.get(it));
		}
		
		return null;
    }
}

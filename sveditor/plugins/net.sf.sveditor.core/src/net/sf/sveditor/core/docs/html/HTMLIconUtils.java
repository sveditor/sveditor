/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 *     Armond Paiva - repurposed from UI for use in HTML doc generation
 ****************************************************************************/


package net.sf.sveditor.core.docs.html;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class HTMLIconUtils implements IHTMLIcons {
	
	private static final Map<String, String>	fImgDescMap ;
	
	static {
		fImgDescMap = new HashMap<String, String>();
//		fImgDescMap.put(DocTopicManager.File, FILE_OBJ);
		fImgDescMap.put(DocTopicManager.TOPIC_MODULE, MODULE_OBJ);
//		fImgDescMap.put(DocTopicManager.InterfaceDecl, INT_OBJ);
//		fImgDescMap.put(DocTopicManager.ConfigDecl, CONFIG_OBJ);
		fImgDescMap.put(DocTopicManager.TOPIC_CLASS, CLASS_OBJ);
//		fImgDescMap.put(DocTopicManager.MacroDef, DEFINE_OBJ);
//		fImgDescMap.put(DocTopicManager.Include, INCLUDE_OBJ);
		fImgDescMap.put(DocTopicManager.TOPIC_PACKAGE, PACKAGE_OBJ);
//		fImgDescMap.put(DocTopicManager.TypeInfoStruct, STRUCT_OBJ);
//		fImgDescMap.put(DocTopicManager.Covergroup, COVERGROUP_OBJ);
//		fImgDescMap.put(DocTopicManager.Coverpoint, COVERPOINT_OBJ);
//		fImgDescMap.put(DocTopicManager.CoverpointCross, COVERPOINT_CROSS_OBJ);
//		fImgDescMap.put(DocTopicManager.Sequence, SEQUENCE_OBJ);
//		fImgDescMap.put(DocTopicManager.Property, PROPERTY_OBJ);
		fImgDescMap.put(DocTopicManager.TOPIC_CONSTRAINT, CONSTRAINT_OBJ);
//		fImgDescMap.put(DocTopicManager.AlwaysStmt, ALWAYS_BLOCK_OBJ);
//		fImgDescMap.put(DocTopicManager.InitialStmt, INITIAL_OBJ);
//		fImgDescMap.put(DocTopicManager.Assign, ASSIGN_OBJ);
//		fImgDescMap.put(DocTopicManager.GenerateBlock, GENERATE_OBJ);
//		fImgDescMap.put(DocTopicManager.ClockingBlock, CLOCKING_OBJ);
//		fImgDescMap.put(DocTopicManager.ImportItem, IMPORT_OBJ);
//		fImgDescMap.put(DocTopicManager.ModIfcInst, MOD_IFC_INST_OBJ);
//		fImgDescMap.put(DocTopicManager.ModIfcInstItem, MOD_IFC_INST_OBJ);
//		fImgDescMap.put(DocTopicManager.VarDeclItem, FIELD_PUB_OBJ);
		fImgDescMap.put(DocTopicManager.TOPIC_TASK, TASK_PUB_OBJ);
		fImgDescMap.put(DocTopicManager.TOPIC_FUNCTION, TASK_PUB_OBJ); // FIXME: image for func?

		/*
//		fImgDescMap.put(DocItemType.File, FILE_OBJ);
//		fImgDescMap.put(DocItemType.ModuleDecl, MODULE_OBJ);
//		fImgDescMap.put(DocItemType.InterfaceDecl, INT_OBJ);
//		fImgDescMap.put(DocItemType.ConfigDecl, CONFIG_OBJ);
		fImgDescMap.put(DocItemType.CLASS, CLASS_OBJ);
//		fImgDescMap.put(DocItemType.MacroDef, DEFINE_OBJ);
//		fImgDescMap.put(DocItemType.Include, INCLUDE_OBJ);
		fImgDescMap.put(DocItemType.PACKAGE, PACKAGE_OBJ);
//		fImgDescMap.put(DocItemType.TypeInfoStruct, STRUCT_OBJ);
//		fImgDescMap.put(DocItemType.Covergroup, COVERGROUP_OBJ);
//		fImgDescMap.put(DocItemType.Coverpoint, COVERPOINT_OBJ);
//		fImgDescMap.put(DocItemType.CoverpointCross, COVERPOINT_CROSS_OBJ);
//		fImgDescMap.put(DocItemType.Sequence, SEQUENCE_OBJ);
//		fImgDescMap.put(DocItemType.Property, PROPERTY_OBJ);
		fImgDescMap.put(DocItemType.Constraint, CONSTRAINT_OBJ);
//		fImgDescMap.put(DocItemType.AlwaysStmt, ALWAYS_BLOCK_OBJ);
//		fImgDescMap.put(DocItemType.InitialStmt, INITIAL_OBJ);
//		fImgDescMap.put(DocItemType.Assign, ASSIGN_OBJ);
//		fImgDescMap.put(DocItemType.GenerateBlock, GENERATE_OBJ);
//		fImgDescMap.put(DocItemType.ClockingBlock, CLOCKING_OBJ);
//		fImgDescMap.put(DocItemType.ImportItem, IMPORT_OBJ);
//		fImgDescMap.put(DocItemType.ModIfcInst, MOD_IFC_INST_OBJ);
//		fImgDescMap.put(DocItemType.ModIfcInstItem, MOD_IFC_INST_OBJ);
//		fImgDescMap.put(DocItemType.VarDeclItem, FIELD_PUB_OBJ);
		fImgDescMap.put(DocItemType.TASK, TASK_PUB_OBJ);
		fImgDescMap.put(DocItemType.FUNC, TASK_PUB_OBJ); // FIXME: image for func?
		*/
	}
	
	private static LogHandle log ;
	
	public static LogHandle getLog() {
		if(log == null) {
			log = LogFactory.getLogHandle("HTMLIconUtils") ;
		}
		return log ;
	}
	
	public static String getImagePath(DocTopic docItem) {
		if (docItem.getTopic() == DocTopicManager.TOPIC_VARIABLE) {
			int attr = docItem.getAttr() ;
			if((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
				return FIELD_PRIV_OBJ ; 
			} else if((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
				return FIELD_PROT_OBJ ; 
			} else { 
				return FIELD_PUB_OBJ ; 
			}
		} else if(docItem.getTopic() == DocTopicManager.TOPIC_TASK) {
			int attr = docItem.getAttr() ;
			if((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
				return TASK_PRIV_OBJ ; 
			} else if((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
				return TASK_PROT_OBJ ; 
			} else { 
				return TASK_PUB_OBJ ; 
			}
		} else { 
			String topic = docItem.getTopic() ; 
			if (fImgDescMap.containsKey(topic)) {
				return fImgDescMap.get(topic) ;
			}
		}
		
		return null;
	}
	
}

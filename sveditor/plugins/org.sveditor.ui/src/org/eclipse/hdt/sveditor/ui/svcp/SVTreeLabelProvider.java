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


package org.eclipse.hdt.sveditor.ui.svcp;

import org.eclipse.hdt.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBAssign;
import org.eclipse.hdt.sveditor.core.db.SVDBAssignItem;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBFunction;
import org.eclipse.hdt.sveditor.core.db.SVDBGenerateBlock;
import org.eclipse.hdt.sveditor.core.db.SVDBGenerateIf;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcClassParam;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInst;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInstItem;
import org.eclipse.hdt.sveditor.core.db.SVDBParamValueAssign;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfo;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfoUserDef;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileStmt;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBAlwaysStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBAssertStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBBlockStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBBodyStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBCoverStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBDefParamItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBEventControlStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBExportItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBExprStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBImportItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBTimePrecisionStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBTimeUnitsStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class SVTreeLabelProvider extends LabelProvider implements IStyledLabelProvider {
	protected boolean							fShowFunctionRetType;
	
	
	private WorkbenchLabelProvider				fLabelProvider;
	
	
	public SVTreeLabelProvider() {
		fLabelProvider = new WorkbenchLabelProvider();
		fShowFunctionRetType = true;
	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof ISVDBItemBase) {
			return SVDBIconUtils.getIcon((ISVDBItemBase)element);
		} else if (element instanceof SVDBDeclCacheItem) {
			SVDBDeclCacheItem item = (SVDBDeclCacheItem)element;
			return SVDBIconUtils.getIcon(item.getType());
		} else {
			return super.getImage(element);
		}
	}
	
	public StyledString getStyledText(Object element) {
		if (element == null) {
			return new StyledString("null");
		}
		
		if (element instanceof SVDBDeclCacheItem) {
			SVDBDeclCacheItem item = (SVDBDeclCacheItem)element;
			return new StyledString(item.getName());
		} else if (element instanceof SVDBVarDeclItem) {
			SVDBVarDeclItem var = (SVDBVarDeclItem)element;
			SVDBVarDeclStmt var_r = var.getParent();
			StyledString ret = new StyledString(var.getName());
			
			if (var_r.getTypeInfo() != null) {
				ret.append(": " + var_r.getTypeName(), StyledString.QUALIFIER_STYLER);
				
				SVDBTypeInfo type = var_r.getTypeInfo();
				
				if (type.getType() == SVDBItemType.TypeInfoUserDef) {
					SVDBTypeInfoUserDef cls = (SVDBTypeInfoUserDef)type;
					if (cls.getParameters() != null && 
							cls.getParameters().getParameters().size() > 0) {
						ret.append("<", StyledString.QUALIFIER_STYLER);
						
						for (int i=0; i<cls.getParameters().getParameters().size(); i++) {
							SVDBParamValueAssign p = 
								cls.getParameters().getParameters().get(i);
							ret.append(p.getName(), StyledString.QUALIFIER_STYLER);
							if (i+1 < cls.getParameters().getParameters().size()) {
								ret.append(", ", StyledString.QUALIFIER_STYLER);
							}
						}
						
						ret.append(">", StyledString.QUALIFIER_STYLER);
					}
				}
			}

			return ret; 
		} else if (element instanceof SVDBGenerateIf) {
			SVDBGenerateIf it = (SVDBGenerateIf)element;
			if (it.fName != null)  {
				return (new StyledString (it.fName));
			}
			// This will occur if a if statement within an initial block etc is suddenly recognized as a "generateif"
			// The parser doesn't do a good job of casting from the if to the genif, and fname seems to be off in the weeds
			// TODO: Fix this properly - See Tracker # 3591399
			else  {
				return (new StyledString ("if"));
			}
		} else if (element instanceof SVDBGenerateBlock) {
			SVDBGenerateBlock it = (SVDBGenerateBlock)element;
			if (it.getName() != null)  {
				return (new StyledString (it.getName()));
			} else  {
				return (new StyledString ("generate"));
			}
		} else if (element instanceof ISVDBNamedItem && ((ISVDBNamedItem)element).getName() != null) {
			StyledString ret = new StyledString(((ISVDBNamedItem)element).getName());
			ISVDBNamedItem ni = (ISVDBNamedItem)element;
			
			if (ni.getType().isElemOf(SVDBItemType.Task, SVDBItemType.Function)) {
				SVDBTask tf = (SVDBTask)element;
				
				ret.append("(");
				for (int i=0; i<tf.getParams().size(); i++) {
					SVDBParamPortDecl p = tf.getParams().get(i);
					if (p.getTypeInfo() != null) {
						ret.append(p.getTypeInfo().toString());
					}
					if (i+1 < tf.getParams().size()) {
						ret.append(", ");
					}
				}
				
				ret.append(")");
				
				if (tf.getType() == SVDBItemType.Function) {
					SVDBFunction f = (SVDBFunction)tf;
					if (f.getReturnType() != null && 
							!f.getReturnType().equals("void") &&
							fShowFunctionRetType) {
						ret.append(": " + f.getReturnType(), StyledString.QUALIFIER_STYLER);
					}
				}
			} else if (element instanceof SVDBModIfcDecl) {
				SVDBModIfcDecl decl = (SVDBModIfcDecl)element;

				if (decl.getParameters().size() > 0) {
					ret.append("<", StyledString.QUALIFIER_STYLER);

					for (int i=0; i<decl.getParameters().size(); i++) {
						SVDBModIfcClassParam p = decl.getParameters().get(i);
						ret.append(p.getName(), StyledString.QUALIFIER_STYLER);

						if (i+1 < decl.getParameters().size()) {
							ret.append(", ", StyledString.QUALIFIER_STYLER);
						}
					}
					
					ret.append(">", StyledString.QUALIFIER_STYLER);
				}
			} else if (element instanceof SVDBClassDecl) {
				SVDBClassDecl decl = (SVDBClassDecl)element;

				if (decl.getParameters() != null && decl.getParameters().size() > 0) {
					ret.append("<", StyledString.QUALIFIER_STYLER);

					for (int i=0; i<decl.getParameters().size(); i++) {
						SVDBModIfcClassParam p = decl.getParameters().get(i);
						ret.append(p.getName(), StyledString.QUALIFIER_STYLER);

						if (i+1 < decl.getParameters().size()) {
							ret.append(", ", StyledString.QUALIFIER_STYLER);
						}
					}
					
					ret.append(">", StyledString.QUALIFIER_STYLER);
				}
			} else if (ni.getType() == SVDBItemType.ModIfcInstItem) {
				SVDBModIfcInstItem mod_item = (SVDBModIfcInstItem)ni;
				SVDBModIfcInst mod_inst = (SVDBModIfcInst)mod_item.getParent();
				
				ret.append(": " + mod_inst.getTypeName(), StyledString.QUALIFIER_STYLER);
			} else if (ni.getType() == SVDBItemType.CoverageOptionStmt) {
//				SVDBCoverageOptionStmt option = (SVDBCoverageOptionStmt)ni;
				ret.append(": option", StyledString.QUALIFIER_STYLER);
			} else {
//				ret = new StyledString("UNKNOWN NamedItem " + ((ISVDBNamedItem)element).getType());
			}
			
			return ret;

		} else if (element instanceof SVDBArgFileStmt) {
			SVDBArgFileStmt stmt = (SVDBArgFileStmt)element;
			String ret = null;
			switch (stmt.getType()) {
				case ArgFilePathStmt:
					ret = ((SVDBArgFilePathStmt)stmt).getPath();
					break;
					
				case ArgFileIncDirStmt:
					ret = ((SVDBArgFileIncDirStmt)stmt).getIncludePath();
					break;
					
				case ArgFileIncFileStmt:
					ret = ((SVDBArgFileIncFileStmt)stmt).getPath();
					break;
					
				case ArgFileDefineStmt: {
					SVDBArgFileDefineStmt ds = (SVDBArgFileDefineStmt)stmt;
					if (ds.getValue() != null) {
						ret = ds.getKey() + " = " + ds.getValue();
					} else {
						ret = ds.getKey();
					}
					} break;
					
				case ArgFileSrcLibPathStmt:
					ret = ((SVDBArgFileSrcLibPathStmt)stmt).getSrcLibPath();
					break;
				
				default:
					ret = stmt.toString();
					break;
			}
			
			return new StyledString(ret);
		} else if (element instanceof ISVDBItemBase) {
			ISVDBItemBase it = (ISVDBItemBase)element;
			StyledString ret = null;
			
			if (it.getType() == SVDBItemType.AlwaysStmt) {
				SVDBAlwaysStmt always = (SVDBAlwaysStmt)it;
				String block_name = "";
				
				if (always.getBody() != null && 
						always.getBody().getType() == SVDBItemType.BlockStmt) {
					block_name = ((SVDBBlockStmt)always.getBody()).getBlockName();
					if (block_name == null) {
						block_name = "";
					}
				}

				if (always.getBody() != null && always.getBody().getType() == SVDBItemType.EventControlStmt) {
					SVDBEventControlStmt stmt = (SVDBEventControlStmt)always.getBody();
					ret = new StyledString(getBodyStmtText(
							stmt.getExpr().toString().trim(), stmt));
				} else {
					ret = new StyledString(getBodyStmtText("always", it));
				}
			} else if (it.getType() == SVDBItemType.InitialStmt) {
				ret = new StyledString(getBodyStmtText("initial", it));
			} else if (it.getType() == SVDBItemType.FinalStmt) {
				ret = new StyledString(getBodyStmtText("final", it));
			} else if (it.getType() == SVDBItemType.ImportItem) {
				SVDBImportItem imp = (SVDBImportItem)it;
				ret = new StyledString("import " + imp.getImport());
			} else if (it.getType() == SVDBItemType.ExportItem) {
				SVDBExportItem exp = (SVDBExportItem)it;
				ret = new StyledString("export " + exp.getExport());
			} else if (it.getType() == SVDBItemType.ModportDecl) {
				ret = new StyledString(getBodyStmtText("modport", it));
			} else if (it.getType() == SVDBItemType.Assign) {
				SVDBAssign assign = (SVDBAssign)it;
				if (assign.getAssignList().size() > 0) {
					SVDBAssignItem assign_it = assign.getAssignList().get(0);
					
					String lhs = null;
					String rhs = null;
					
					if (assign_it != null) {
						if (assign_it.getLHS() != null) {
							lhs = assign_it.getLHS().toString();
						}
						if (assign_it.getRHS() != null) {
							rhs = assign_it.getRHS().toString();
						}
					}
					
					ret = new StyledString("" + lhs + " = " + rhs);
				} else {
					ret = new StyledString("assign");
				}
			} else if (it.getType() == SVDBItemType.ArgFilePathStmt) {
				SVDBArgFilePathStmt path = (SVDBArgFilePathStmt)it;
				ret = new StyledString("path: " + path.getPath());
			} else if (it.getType() == SVDBItemType.DefParamItem) {
				SVDBDefParamItem dp = (SVDBDefParamItem)it;
				String str = "defparam: ";
				
				if (dp.getTarget() != null) {
					str += dp.getTarget().toString();
					if (dp.getExpr() != null) {
						str += " = " + dp.getExpr().toString();
					}
				}
				ret = new StyledString(str);
			} else if (it.getType() == SVDBItemType.AssertStmt) {
				SVDBAssertStmt asrt = (SVDBAssertStmt)it;
				String str = "assert";
				if (asrt.getName() != null)  {
					str += ": " + asrt.getName();
				}
				ret = new StyledString(str);
			} else if (it.getType() == SVDBItemType.TimePrecisionStmt) {
				SVDBTimePrecisionStmt tps = (SVDBTimePrecisionStmt) it;
				String str = "timeprecision";
				if (tps.getArg1() != null)  {
					str += ": " + tps.getArg1();
				}
				ret = new StyledString(str);
			} else if (it.getType() == SVDBItemType.TimeUnitsStmt) {
				SVDBTimeUnitsStmt tus = (SVDBTimeUnitsStmt) it;
				String str = "timeprecision";
				if (tus.getUnits() != null)  {
					str += ": " + tus.getUnits();
				}
				if (tus.getPrecision() != null)  {
					str += "/ " + tus.getPrecision();
				}
				ret = new StyledString(str);
			} else if (it.getType() == SVDBItemType.ExprStmt) {
				SVDBExprStmt es = (SVDBExprStmt) it;
				String str = "expression";
				if (es.fExpr.toString() != null)  {
					str = es.fExpr.toString();
				}
				ret = new StyledString(str);
			} else if (it.getType() == SVDBItemType.CoverStmt) {
				SVDBCoverStmt es = (SVDBCoverStmt) it;
				String str = "cover";
				if (es.fName != null)  {
					str = es.fName;
				}
				ret = new StyledString(str);
			}
			
			if (ret == null) {
				ret = new StyledString(element.toString());
			}
			return ret;
		} else {
			return new StyledString(element.toString());
		}
	}
	
	private String getBodyStmtText(String base, ISVDBItemBase it) {
		if (it instanceof SVDBBodyStmt) {
			SVDBBodyStmt stmt = (SVDBBodyStmt)it;
			if (stmt.getBody() instanceof SVDBBlockStmt) {
				SVDBBlockStmt block = (SVDBBlockStmt)stmt.getBody();
				if (block.getBlockName() != null && !block.getBlockName().equals("")) {
					if (base.equals("")) {
						return block.getBlockName();
					} else {
						return block.getBlockName() + ": " + base;
					}
//					return base + " : " + block.getBlockName();
				}
			}
		}
		return base;
	}

	@Override
	public String getText(Object element) {
		return getStyledText(element).toString();
	}

	@Override
	public void addListener(ILabelProviderListener listener) {
		fLabelProvider.addListener(listener);
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
		fLabelProvider.removeListener(listener);
	}
	
	@Override
	public boolean isLabelProperty(Object element, String property) {
		return fLabelProvider.isLabelProperty(element, property);
	}

	@Override
	public void dispose() {
		super.dispose();
		fLabelProvider.dispose();
	}
}

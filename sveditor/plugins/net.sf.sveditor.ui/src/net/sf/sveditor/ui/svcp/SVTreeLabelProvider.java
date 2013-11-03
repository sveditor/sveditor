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

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBAssignItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBGenerateIf;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileStmt;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBEventControlStmt;
import net.sf.sveditor.core.db.stmt.SVDBExportItem;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
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
				ret.append(" : " + var_r.getTypeName(), StyledString.QUALIFIER_STYLER);
				
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
		} else if (element instanceof ISVDBNamedItem) {
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
				
				ret.append(" : " + mod_inst.getTypeName(), StyledString.QUALIFIER_STYLER);
			} else if (ni.getType() == SVDBItemType.CoverageOptionStmt) {
//				SVDBCoverageOptionStmt option = (SVDBCoverageOptionStmt)ni;
				ret.append(" : option", StyledString.QUALIFIER_STYLER);
			} else {
//				ret = new StyledString("UNKNOWN NamedItem " + ((ISVDBNamedItem)element).getType());
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
				if (always.getBody() != null && always.getBody().getType() == SVDBItemType.EventControlStmt) {
					SVDBEventControlStmt stmt = (SVDBEventControlStmt)always.getBody();
					ret = new StyledString(stmt.getExpr().toString().trim());
				} else {
					ret = new StyledString("always");
				}
			} else if (it.getType() == SVDBItemType.InitialStmt) {
				ret = new StyledString("initial");
			} else if (it.getType() == SVDBItemType.FinalStmt) {
				ret = new StyledString("final");
			} else if (it.getType() == SVDBItemType.ImportItem) {
				SVDBImportItem imp = (SVDBImportItem)it;
				ret = new StyledString("import " + imp.getImport());
			} else if (it.getType() == SVDBItemType.ExportItem) {
				SVDBExportItem exp = (SVDBExportItem)it;
				ret = new StyledString("export " + exp.getExport());
			} else if (it.getType() == SVDBItemType.Assign) {
				SVDBAssign assign = (SVDBAssign)it;
				if (assign.getAssignList().size() > 0) {
					SVDBAssignItem assign_it = assign.getAssignList().get(0);
					
					ret = new StyledString(
							assign_it.getLHS().toString() + 
							" = " + 
							assign_it.getRHS().toString());
				} else {
					ret = new StyledString("assign");
				}
			} else if (it.getType() == SVDBItemType.ArgFilePathStmt) {
				SVDBArgFilePathStmt path = (SVDBArgFilePathStmt)it;
				ret = new StyledString("path : " + path.getPath());
			}
			
			if (ret == null) {
				ret = new StyledString(element.toString());
			}
			return ret;
		} else {
			return new StyledString(element.toString());
		}
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

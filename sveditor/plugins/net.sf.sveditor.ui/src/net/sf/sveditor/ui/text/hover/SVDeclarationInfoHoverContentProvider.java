package net.sf.sveditor.ui.text.hover;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBInterfaceDecl;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.SVDBProgramDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDeclarationInfoHoverContentProvider extends
		SVHoverContentProvider {
	
	public static final Set<SVDBItemType>			SUPPORTED_TYPES;
	
	static {
		SUPPORTED_TYPES = new HashSet<SVDBItemType>();
		SUPPORTED_TYPES.add(SVDBItemType.VarDeclItem);
		SUPPORTED_TYPES.add(SVDBItemType.ClassDecl);
		SUPPORTED_TYPES.add(SVDBItemType.InterfaceDecl);
		SUPPORTED_TYPES.add(SVDBItemType.ModuleDecl);
		SUPPORTED_TYPES.add(SVDBItemType.ProgramDecl);
		SUPPORTED_TYPES.add(SVDBItemType.MacroDef);
		SUPPORTED_TYPES.add(SVDBItemType.ModIfcClassParam);
	}
	
	public SVDeclarationInfoHoverContentProvider() {
		super(null);
		fLog = LogFactory.getLogHandle("SVDeclarationInfoHoverContentProvider");
	}

	@Override
	public String getContent(SVHoverInformationControlInput input) {
		StringBuilder sb = new StringBuilder();
		if (fContent != null) {
			return fContent;
		}
		
		ISVDBItemBase item = input.getElement();
//		ISVDBScopeItem scope = input.getScope();
		
		if (item.getType() == SVDBItemType.VarDeclItem) {
			SVDBVarDeclItem var_item = (SVDBVarDeclItem)item;
			SVDBVarDeclStmt var_stmt = (SVDBVarDeclStmt)var_item.getParent();

			if (var_stmt.getTypeName() != null) {
				sb.append(var_stmt.getTypeName() + " ");
			}
			
			sb.append(var_item.getName());

			// Append the name of the scope that contains the declaration
			ISVDBChildItem ci = var_stmt.getParent();
			while (ci != null && !(ci instanceof ISVDBScopeItem) && 
					!(ci instanceof ISVDBNamedItem)) {
				ci = ci.getParent();
			}
			
			if (ci != null) {
				sb.append(" - " + SVDBItem.getName(ci));
			}
		} else if (item.getType() == SVDBItemType.ModIfcClassParam) {
			SVDBModIfcClassParam p = (SVDBModIfcClassParam)item;
			
			sb.append(p.getName());
			
			if (p.getDefault() != null) {
				sb.append(" = ");
				sb.append(p.getDefault().toString());
			}
			
		} else if (item.getType() == SVDBItemType.MacroDef) {
			SVDBMacroDef d = (SVDBMacroDef)item;
			sb.append("Macro " + d.getName());
			if (d.getParameters() != null && d.getParameters().size() > 0) {
				sb.append("(");
				for (int i=0; i<d.getParameters().size(); i++) {
					SVDBMacroDefParam p = d.getParameters().get(i);
					sb.append(p.getName());
					if (i+1 < d.getParameters().size()) {
						sb.append(", ");
					}
				}
				sb.append(")");
			}
			
			sb.append(" : " + d.getDef());
		} else if (item.getType() == SVDBItemType.ClassDecl) {
			SVDBClassDecl cls = (SVDBClassDecl)item;
			sb.append("Class " + cls.getName());
		} else if (item.getType() == SVDBItemType.InterfaceDecl) {
			SVDBInterfaceDecl ifc = (SVDBInterfaceDecl)item;
			sb.append("Interface " + ifc.getName());
		} else if (item.getType() == SVDBItemType.ModuleDecl) {
			SVDBModuleDecl mod = (SVDBModuleDecl)item;
			sb.append("Module " + mod.getName());
		} else if (item.getType() == SVDBItemType.ProgramDecl) {
			SVDBProgramDecl pgm = (SVDBProgramDecl)item;
			sb.append("Program " + pgm.getName());
		}

		
		if (sb.length() > 0) {
			fContent = sb.toString();
		} else {
			fContent = "Unsupported element: " + input.getElement().getType();
		}
		
		return fContent;
	}
	
}

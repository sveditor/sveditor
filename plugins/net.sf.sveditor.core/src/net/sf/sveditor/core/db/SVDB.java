package net.sf.sveditor.core.db;

public class SVDB {
	private static boolean			fInit;
	
	public static void init() {
		if (fInit) {
			return;
		}
		
		SVDBAlwaysBlock.init();
		SVDBAssign.init();
		SVDBConstraint.init();
		SVDBCoverGroup.init();
		SVDBCoverPoint.init();
		SVDBCoverpointCross.init();
		SVDBFile.init();
		SVDBInclude.init();
		SVDBInitialBlock.init();
		SVDBMacroDef.init();
		SVDBMarkerItem.init();
		SVDBModIfcClassDecl.init();
		SVDBModIfcClassParam.init();
		SVDBModIfcInstItem.init();
		SVDBPackageDecl.init();
		SVDBPreProcCond.init();
		SVDBProgramBlock.init();
		SVDBScopeItem.init();
		SVDBTaskFuncParam.init();
		SVDBTaskFuncScope.init();
		SVDBTypedef.init();
		SVDBTypeInfo.init();
		SVDBVarDeclItem.init();

		fInit = true;
	}

}

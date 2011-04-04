package net.sf.sveditor.core.tests.db;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDB;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBClockingBlock;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBCoverpoint;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt;
import net.sf.sveditor.core.db.stmt.SVDBAlwaysStmt.AlwaysType;
import net.sf.sveditor.core.db.stmt.SVDBImportStmt;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;

public class TestInitDuplicate extends TestCase {

	public void disabled_testSVDBDumpLoad() throws DBFormatException, DBWriteException {
		SVDB.init();
		
		int_testDumpLoad(new SVDBAlwaysStmt(AlwaysType.Always));
		int_testDumpLoad(new SVDBAssign());
		int_testDumpLoad(new SVDBClockingBlock("clocking"));
		int_testDumpLoad(new SVDBConstraint());
		int_testDumpLoad(new SVDBCovergroup("cg"));
		int_testDumpLoad(new SVDBCoverpoint("cp"));
		int_testDumpLoad(new SVDBCoverpointCross("cross"));
		
		int_testDumpLoad(new SVDBGenerateBlock("generate"));
		int_testDumpLoad(new SVDBImportStmt());
		int_testDumpLoad(new SVDBInclude("include"));
		
		{
			List<String> params = new ArrayList<String>();
			int_testDumpLoad(new SVDBMacroDef("macro", params, "definition"));

			params.add("p1");
			params.add("p2");
			int_testDumpLoad(new SVDBMacroDef("macro", params, "definition"));
			int_testDumpLoad(new SVDBClassDecl("class"));
		}

		{
			SVDBClassDecl cls = new SVDBClassDecl("class");
			SVDBModIfcClassParam p = new SVDBModIfcClassParam("param");
			p.setLocation(new SVDBLocation(1, 1));
			cls.getParameters().add(p);
			int_testDumpLoad(cls);
		}
		
		int_testDumpLoad(new SVDBModIfcInst(new SVDBTypeInfoUserDef("m1")));
		int_testDumpLoad(new SVDBPackageDecl("pkg"));
		
		{
			SVDBParamPortDecl p;
			SVDBFunction tf = new SVDBFunction("func", new SVDBTypeInfoBuiltin("int"));
			p = new SVDBParamPortDecl(new SVDBTypeInfoBuiltin("int"));
			p.addVar(new SVDBVarDeclItem("p1"));
			p.setLocation(new SVDBLocation(1, 1));
			tf.getParams().add(p);
			
			int_testDumpLoad(tf);
		}
		
	}
	
	private void int_testDumpLoad(ISVDBItemBase item) throws DBFormatException, DBWriteException {
		ByteOutputStream bos = new ByteOutputStream();
		SVDBPersistenceWriter writer = new SVDBPersistenceWriter(bos);
		
		// Give the item a location so comparison is correct
		item.setLocation(new SVDBLocation(1, 1));
		if (item instanceof ISVDBScopeItem) {
			((ISVDBScopeItem)item).setEndLocation(new SVDBLocation(2, 1));
		}
		
		writer.writeSVDBItem(item);
		writer.close();

		SVDBPersistenceReader reader = new SVDBPersistenceReader(
				new ByteArrayInputStream(bos.getBytes()));
		
		SVDBFile file = new SVDBFile("foo");
		SVDBScopeItem parent = null;
		
		ISVDBItemBase load = reader.readSVDBItem(parent);
		
		boolean eq = item.equals(load);
		if (!eq) {
			System.out.println("Dump/load of " + item.getType() + " failed");
			item.equals(load);
		}
		assertTrue(eq);
	}

}

package net.sf.sveditor.core.tests.db;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDB;
import net.sf.sveditor.core.db.SVDBAlwaysBlock;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBClockingBlock;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBCoverPoint;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
import net.sf.sveditor.core.db.SVDBImport;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBInitialBlock;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;
import net.sf.sveditor.core.db.stmt.SVDBParamPort;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;

public class TestInitDuplicate extends TestCase {

	public void testSVDBDumpLoad() throws DBFormatException {
		SVDB.init();
		
		int_testDumpLoad(new SVDBAlwaysBlock("expr"));
		int_testDumpLoad(new SVDBAssign("target"));
		int_testDumpLoad(new SVDBClockingBlock("clocking"));
		int_testDumpLoad(new SVDBConstraint("c"));
		int_testDumpLoad(new SVDBCoverGroup("cg"));
		int_testDumpLoad(new SVDBCoverPoint("cp"));
		int_testDumpLoad(new SVDBCoverpointCross("cross"));
		
		int_testDumpLoad(new SVDBGenerateBlock("generate"));
		int_testDumpLoad(new SVDBImport("import"));
		int_testDumpLoad(new SVDBInclude("include"));
		int_testDumpLoad(new SVDBInitialBlock());
		
		{
			List<String> params = new ArrayList<String>();
			int_testDumpLoad(new SVDBMacroDef("macro", params, "definition"));

			params.add("p1");
			params.add("p2");
			int_testDumpLoad(new SVDBMacroDef("macro", params, "definition"));
			int_testDumpLoad(new SVDBModIfcClassDecl("class", SVDBItemType.Class));
		}

		{
			SVDBModIfcClassDecl cls = new SVDBModIfcClassDecl("class", SVDBItemType.Class);
			SVDBModIfcClassParam p = new SVDBModIfcClassParam("param");
			p.setLocation(new SVDBLocation(1, 1));
			cls.getParameters().add(p);
			int_testDumpLoad(cls);
		}
		
		int_testDumpLoad(new SVDBModIfcInstItem(new SVDBTypeInfoUserDef("m1"), "m1"));
		int_testDumpLoad(new SVDBPackageDecl("pkg"));
		
		{
			SVDBParamPort p;
			SVDBTaskFuncScope tf = new SVDBTaskFuncScope("func", SVDBItemType.Function);
			tf.setReturnType(new SVDBTypeInfoBuiltin("int"));
			p = new SVDBParamPort(new SVDBTypeInfoBuiltin("int"));
			p.addVar(new SVDBVarDeclItem("p1"));
			p.setLocation(new SVDBLocation(1, 1));
			tf.getParams().add(p);
			
			int_testDumpLoad(tf);
		}
		
	}
	
	private void int_testDumpLoad(ISVDBItemBase item) throws DBFormatException {
		ByteOutputStream bos = new ByteOutputStream();
		SVDBPersistenceWriter writer = new SVDBPersistenceWriter(bos);
		
		// Give the item a location so comparison is correct
		item.setLocation(new SVDBLocation(1, 1));
		if (item instanceof ISVDBScopeItem) {
			((ISVDBScopeItem)item).setEndLocation(new SVDBLocation(2, 1));
		}
		
		item.dump(writer);
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

/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.index.SVDBIndexCacheData;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;

public class TestIndexCacheDataPersistence extends TestCase {
	
	private void dump_load(
			SVDBIndexCacheData		data,
			SVDBIndexCacheData		data_n) throws DBFormatException, DBWriteException, IOException {
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutputStream dos = new DataOutputStream(bos);

		IDBWriter writer = new SVDBPersistenceRW();
		IDBReader reader = new SVDBPersistenceRW();

		writer.init(dos);
		writer.writeObject(data.getClass(), data);
		dos.flush();

		DataInputStream dis = new DataInputStream(new ByteArrayInputStream(bos.toByteArray()));
		reader.init(dis);
		reader.readObject(null, data_n.getClass(), data_n);
	}
	
	public void testBasics() throws DBFormatException, DBWriteException, IOException {
		SVDBIndexCacheData data = new SVDBIndexCacheData("base");
		SVDBIndexCacheData data_n = new SVDBIndexCacheData("base2");

		dump_load(data, data_n);
		
		assertEquals(data.getBaseLocation(), data_n.getBaseLocation());
	}

	public void testDeclCache() throws DBFormatException, DBWriteException, IOException {
		fail("Direct use of the cache API: FIXME");
//		SVDBBaseIndexCacheData data = new SVDBBaseIndexCacheData("base");
//		SVDBBaseIndexCacheData data_n = new SVDBBaseIndexCacheData("base2");
//	
//		data.getDeclCacheMap().put("my_file", new ArrayList<SVDBDeclCacheItem>());
//		data.getDeclCacheMap().get("my_file").add(new SVDBDeclCacheItem(null, "my_file", "my_item", SVDBItemType.ClassDecl, false));
//
//		dump_load(data, data_n);
//		
//		assertEquals(data.getBaseLocation(), data_n.getBaseLocation());
//		assertEquals(1, data_n.getDeclCacheMap().size());
//		assertEquals("my_item", data_n.getDeclCacheMap().get("my_file").get(0).getName());
	}

}

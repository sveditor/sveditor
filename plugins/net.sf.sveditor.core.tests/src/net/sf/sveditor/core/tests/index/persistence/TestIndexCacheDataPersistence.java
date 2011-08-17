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
import java.util.ArrayList;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;

public class TestIndexCacheDataPersistence extends TestCase {
	
	private void dump_load(
			SVDBBaseIndexCacheData		data,
			SVDBBaseIndexCacheData		data_n) throws DBFormatException, DBWriteException, IOException {
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutputStream dos = new DataOutputStream(bos);

		SVDBPersistenceWriter writer = new SVDBPersistenceWriter();
		SVDBPersistenceReader reader = new SVDBPersistenceReader();

		writer.init(dos);
		writer.writeObject(data.getClass(), data);
		dos.flush();

		DataInputStream dis = new DataInputStream(new ByteArrayInputStream(bos.toByteArray()));
		reader.init(dis);
		reader.readObject(null, data_n.getClass(), data_n);
	}
	
	public void testBasics() throws DBFormatException, DBWriteException, IOException {
		SVDBBaseIndexCacheData data = new SVDBBaseIndexCacheData("base");
		SVDBBaseIndexCacheData data_n = new SVDBBaseIndexCacheData("base2");

		dump_load(data, data_n);
		
		assertEquals(data.getBaseLocation(), data_n.getBaseLocation());
	}

	public void testDeclCache() throws DBFormatException, DBWriteException, IOException {
		SVDBBaseIndexCacheData data = new SVDBBaseIndexCacheData("base");
		SVDBBaseIndexCacheData data_n = new SVDBBaseIndexCacheData("base2");
		
		data.getDeclCacheMap().put("my_file", new ArrayList<SVDBDeclCacheItem>());
		data.getDeclCacheMap().get("my_file").add(new SVDBDeclCacheItem(null, "my_file", "my_item", SVDBItemType.ClassDecl));

		dump_load(data, data_n);
		
		assertEquals(data.getBaseLocation(), data_n.getBaseLocation());
		assertEquals(1, data_n.getDeclCacheMap().size());
		assertEquals("my_item", data_n.getDeclCacheMap().get("my_file").get(0).getName());
	}

}

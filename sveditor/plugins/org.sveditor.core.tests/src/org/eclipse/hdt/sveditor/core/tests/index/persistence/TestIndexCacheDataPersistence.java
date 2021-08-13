/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.util.ArrayList;

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.SVDBBaseIndexCacheData;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.persistence.DBFormatException;
import org.eclipse.hdt.sveditor.core.db.persistence.DBWriteException;
import org.eclipse.hdt.sveditor.core.db.persistence.IDBReader;
import org.eclipse.hdt.sveditor.core.db.persistence.IDBWriter;
import org.eclipse.hdt.sveditor.core.db.persistence.SVDBPersistenceRW;

import junit.framework.TestCase;

public class TestIndexCacheDataPersistence extends TestCase {
	
	private void dump_load(
			SVDBBaseIndexCacheData		data,
			SVDBBaseIndexCacheData		data_n) throws DBFormatException, DBWriteException, IOException {
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
		SVDBBaseIndexCacheData data = new SVDBBaseIndexCacheData("base");
		SVDBBaseIndexCacheData data_n = new SVDBBaseIndexCacheData("base2");

		dump_load(data, data_n);
		
		assertEquals(data.getBaseLocation(), data_n.getBaseLocation());
	}

	public void testDeclCache() throws DBFormatException, DBWriteException, IOException {
		SVDBBaseIndexCacheData data = new SVDBBaseIndexCacheData("base");
		SVDBBaseIndexCacheData data_n = new SVDBBaseIndexCacheData("base2");
		
		data.getDeclCacheMap().put("my_file", new ArrayList<SVDBDeclCacheItem>());
		data.getDeclCacheMap().get("my_file").add(new SVDBDeclCacheItem(null, "my_file", "my_item", SVDBItemType.ClassDecl, false));

		dump_load(data, data_n);
		
		assertEquals(data.getBaseLocation(), data_n.getBaseLocation());
		assertEquals(1, data_n.getDeclCacheMap().size());
		assertEquals("my_item", data_n.getDeclCacheMap().get("my_file").get(0).getName());
	}

}

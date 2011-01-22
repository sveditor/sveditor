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


package net.sf.sveditor.core.db.persistence;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBDump {
	private LogHandle						fLog;
	private SVDBPersistenceWriter			fWriter;
	private String							fVersion;
	
	public SVDBDump(String version) {
		fLog = LogFactory.getLogHandle("SVDBDump");
		fWriter = new SVDBPersistenceWriter(null);
		fVersion = version;
	}
	
	public void dump(ISVDBIndex index, OutputStream out) {
		ByteArrayOutputStream	index_data_bos = new ByteArrayOutputStream();
		SVDBPersistenceWriter	index_data = new SVDBPersistenceWriter(index_data_bos);
		NullProgressMonitor monitor = new NullProgressMonitor();
		
		fWriter.init(out);
		
		try {
			index.dump(index_data);
			index_data.close();
			index.getBaseLocation();
		} catch (Exception e) {
			fLog.error("Problem while dumping index-specific data", e);
		}
		
		// TODO: Write DB header
		fWriter.writeRawString("SDB<" + index.getBaseLocation() + "::" + fVersion + ">");
		
		// Write back the index-specific data
		fWriter.writeByteArray(index_data_bos.toByteArray());
		
		fLog.debug("dump " + index.getBaseLocation() + 
				": list.size=" + index.getPreProcFileMap(monitor).values().size() +
				" ; db.size=" + index.getFileDB(monitor).values().size());
		fLog.debug("--> write pre-proc map");
		fWriter.writeItemList(index.getPreProcFileMap(monitor).values());
		fLog.debug("<-- write pre-proc map");
		fLog.debug("--> write index map");
		fWriter.writeItemList(index.getFileDB(monitor).values());
		fLog.debug("<-- write index map");
		
		// Ensure any cached data is written back
		fWriter.close();
	}
	
}

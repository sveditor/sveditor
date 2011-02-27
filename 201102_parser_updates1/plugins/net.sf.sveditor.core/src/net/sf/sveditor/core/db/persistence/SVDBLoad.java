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

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBLoad {
	private StringBuilder			fTmpBuffer = new StringBuilder();
	private LogHandle				fLog;
	private SVDBPersistenceReader	fReader;
	private String					fVersion;
	
	public SVDBLoad(String version) {
		fReader = new SVDBPersistenceReader(null);
		fLog = LogFactory.getLogHandle("SVDBLoad");
		fVersion = version;
	}
	
	public String readBaseLocation(InputStream in) throws DBFormatException {
		fReader.init(in);
		
		return fReader.readBaseLocation();
	}
	
	@SuppressWarnings("unchecked")
	public void load(ISVDBIndex index, InputStream in) throws DBFormatException {
		IDBReader		index_data = null;
		
		fReader.init(in);

		String SDB = fReader.readTypeString();
		
		if (!"SDB".equals(SDB)) {
			throw new DBFormatException("Database not prefixed with SDB");
		}
		
		int ch;
		
		if ((ch = fReader.getch()) != '<') {
			throw new DBFormatException("Missing '<'");
		}
		
		fTmpBuffer.setLength(0);
		
		while ((ch = fReader.getch()) != -1 && ch != '>') {
			fTmpBuffer.append((char)ch);
		}
		
		if (ch != '>') {
			throw new DBFormatException("Unterminated SDB record");
		}
		
		int version_idx = fTmpBuffer.indexOf("::");
		String version = "";
		if (version_idx != -1) {
			version = fTmpBuffer.substring(version_idx+2);
			fTmpBuffer.setLength(version_idx+1);
		}

		// Bail if the database version is wrong
		if (!fVersion.equals(version)) {
			throw new DBVersionException("Database version is \"" + version + 
					"\" SVEditor version is \"" + fVersion + "\"");
		}
		
		byte [] index_data_arr = fReader.readByteArray();
		
		if (index_data_arr != null) {
			index_data = new SVDBPersistenceReader(
					new ByteArrayInputStream(index_data_arr));
		}
		
		// TODO: Check base location against index being loaded
		List<SVDBFile> pp_list = (List<SVDBFile>)fReader.readItemList(null);
		List<SVDBFile> db_list = (List<SVDBFile>)fReader.readItemList(null);
		
		fLog.debug("pp_list.size=" + pp_list.size() + 
				" db_list.size=" + db_list.size());
		
		index.load(index_data, pp_list, db_list);
	}
	
}

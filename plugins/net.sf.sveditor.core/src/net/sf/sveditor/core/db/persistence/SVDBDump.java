package net.sf.sveditor.core.db.persistence;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBDump implements IDBWriter {
	private OutputStream					fOut;
	private StringBuilder					fBuf;
	private LogHandle						fLog;
	
	public SVDBDump() {
		fLog = LogFactory.getDefault().getLogHandle("SVDBDump");
	}
	
	public void dump(ISVDBIndex index, OutputStream out) {
		ByteArrayOutputStream	index_data_bos = new ByteArrayOutputStream();
		SVDBPersistenceWriter	index_data = new SVDBPersistenceWriter(index_data_bos);
		fOut    = out;
		fBuf    = new StringBuilder();
		
		try {
			index.dump(index_data);
			index_data.close();
			index.getBaseLocation();
		} catch (Exception e) {
			fLog.error("Problem while dumping index-specific data", e);
		}
		
		// TODO: Write DB header
		writeRawString("SDB<" + index.getBaseLocation() + ">");
//		writeString("DBT<" + index.getTypeID() + ">");
		
		// Write back the index-specific data
		writeByteArray(index_data_bos.toByteArray());
		
		fLog.debug("dump " + index.getBaseLocation() + 
				": list.size=" + index.getPreProcFileMap().values().size() +
				" ; db.size=" + index.getFileDB().values().size());
		fLog.debug("--> write pre-proc map");
		writeItemList(index.getPreProcFileMap().values());
		fLog.debug("<-- write pre-proc map");
		fLog.debug("--> write index map");
		writeItemList(index.getFileDB().values());
		fLog.debug("<-- write index map");
		
		if (fBuf.length() > 0) {
			try {
				byte data[] = fBuf.toString().getBytes();
				fOut.write(data, 0, data.length);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	public void writeInt(int val) {
		writeRawString("I<" + Integer.toHexString(val) + ">");
	}

	public void writeItemType(SVDBItemType type) {
		writeRawString("IT<" + type.toString() + ">");
	}

	public void writeLong(long val) {
		writeRawString("L<" + Long.toHexString(val) + ">");
	}

	public void writeString(String val) {
		if (val == null) {
			writeRawString("S<<-1>>");
		} else {
			writeRawString("S<<" + val.length() + ">" + val + ">");
		}
	}
	
	public void writeByteArray(byte data[]) {
		if (data == null) {
			writeRawString("BA<<-1>>");
		} else {
			writeRawString("BA<<" + data.length + ">");
			for (int i=0; i<data.length; i++) {
				writeRawString("" + data[i]);
				if (i+1 < data.length) {
					writeRawString(",");
				}
			}
			writeRawString(">");
		}
	}

	public void writeRawString(String sval) {
		
		fBuf.append(sval);

		if (fBuf.length() > 1024*1024) {
			byte data[] = fBuf.toString().getBytes();
			try {
				fOut.write(data, 0, data.length);
			} catch (IOException e) { }
			fBuf.setLength(0);
		}
	}

	@SuppressWarnings("unchecked")
	public void writeItemList(Collection items) {
		if (items == null) {
			writeRawString("SIL<-1>");
		} else {
			writeRawString("SIL<" + items.size() + ">");
		
			for (Object it : items) {
				((SVDBItem)it).dump(this);
			}
		}
	}
	
	public void writeStringList(List<String> items) {
		if (items == null) {
			writeRawString("SSL<-1>");
		} else {
			writeRawString("SSL<" + items.size() + ">");
		
			for (String s: items) {
				writeString(s);
			}
		}
	}

	public void writeIntList(List<Integer> items) {
		if (items == null) {
			writeRawString("SNL<-1>");
		} else {
			writeRawString("SNL<" + items.size() + ">");
		
			for (Integer i: items) {
				writeInt(i);
			}
		}
	}
	
}

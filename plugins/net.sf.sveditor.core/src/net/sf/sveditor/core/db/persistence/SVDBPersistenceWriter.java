package net.sf.sveditor.core.db.persistence;

import java.io.IOException;
import java.io.OutputStream;
import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBPersistenceWriter implements IDBWriter {
	private OutputStream				fOutputStream;
	private StringBuilder				fBuf;
	
	public SVDBPersistenceWriter(OutputStream out) {
		fOutputStream = out;
		fBuf = new StringBuilder();
	}
	
	public void close() {
		if (fBuf.length() > 0) {
			try {
				byte data[] = fBuf.toString().getBytes();
				fOutputStream.write(data, 0, data.length);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	public void writeInt(int val) {
		writeRawString("I<" + Integer.toHexString(val) + ">");
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
	
	public void writeRawString(String sval) {
		
		fBuf.append(sval);

		if (fBuf.length() > 1024*1024) {
			byte data[] = fBuf.toString().getBytes();
			try {
				fOutputStream.write(data, 0, data.length);
			} catch (IOException e) { }
			fBuf.setLength(0);
		}
	}
}

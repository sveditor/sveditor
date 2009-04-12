package net.sf.sveditor.core.db.persistence;

import java.io.IOException;
import java.io.OutputStream;
import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;

public class SVDBDump implements IDBWriter {
	private OutputStream					fOut;
	private StringBuilder					fBuf;
	
	public void dump(ISVDBIndex index, OutputStream out) {
		fOut    = out;
		fBuf    = new StringBuilder();

		index.getBaseLocation();
		
		// TODO: Write DB header
		writeRawString("SDB<" + index.getBaseLocation().getPath() + ">");
//		writeString("DBT<" + index.getTypeID() + ">");
		
		System.out.println("dump " + index.getBaseLocation().getPath() + 
				": list.size=" + index.getPreProcFileMap().values().size() +
				" ; db.size=" + index.getFileDB().values().size());
		System.out.println("--> write pre-proc map");
		writeItemList(index.getPreProcFileMap().values());
		System.out.println("<-- write pre-proc map");
		System.out.println("--> write index map");
		writeItemList(index.getFileDB().values());
		System.out.println("<-- write index map");
		
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
}

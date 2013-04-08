package net.sf.sveditor.core.db.index.cache.file;

import java.io.DataOutput;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class SVDBFileSystemDataOutput implements DataOutput {
	private static final int				PAGE_SIZE = 4096;
	
	// List of 4k pages
	private List<byte[]>					fPages;
	private int								fPageIdx;
	
	public SVDBFileSystemDataOutput() {
		fPages = new ArrayList<byte[]>();
		fPages.add(new byte[PAGE_SIZE]);
		fPageIdx = 0;
	}
	
	
	public int getLength() {
		return (PAGE_SIZE * (fPages.size()-1)) + fPageIdx;
	}
	
	public byte[] getPage(int idx) {
		return fPages.get(idx);
	}

	public void write(int val) throws IOException {
		writeByte(val);
	}

	public void write(byte[] val) throws IOException {
		write(val, 0, val.length);
	}

	public void write(byte[] val, int off, int len) throws IOException {
		byte data[] = fPages.get(fPages.size()-1);
		
		for (int i=0; i<len; i++) {
			if (fPageIdx >= data.length) {
				data = new_page();
			}
		
			while (i<len && fPageIdx < data.length) {
				data[fPageIdx++] = val[off+i];
				i++;
			}
		}
	}

	public void writeByte(int val) throws IOException {
		byte data[] = fPages.get(fPages.size()-1);
		
		if (fPageIdx >= data.length) {
			data = new_page();
		}
		data[fPageIdx++] = (byte)val;
	}

	public void writeBytes(String val) throws IOException {
		write(val.getBytes());
	}

	public void writeInt(int val) throws IOException {
		if (fPageIdx+4 <= fPages.get(fPages.size()-1).length) {
			byte data[] = fPages.get(fPages.size()-1);
			byte tmp;
			
			tmp = (byte)(val >> 0);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 8);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 16);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 24);
			data[fPageIdx++] = tmp;
		} else {
			byte data[] = fPages.get(fPages.size()-1);
			byte tmp;
			
			for (int i=0; i<4; i++) {
				if (fPageIdx >= data.length) {
					// Add a new page
					data = new_page();
				}
				tmp = (byte)(val >> 8*i);
				data[fPageIdx++] = tmp;
			}
		}
	}

	public void writeLong(long val) throws IOException {
		if (fPageIdx+8 <= fPages.get(fPages.size()-1).length) {
			byte data[] = fPages.get(fPages.size()-1);
			byte tmp;
			
			tmp = (byte)(val >> 0);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 8);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 16);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 24);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 32);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 40);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 48);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 56);
			data[fPageIdx++] = tmp;
		} else {
			byte data[] = fPages.get(fPages.size()-1);
			byte tmp;
			
			for (int i=0; i<8; i++) {
				if (fPageIdx >= data.length) {
					// Add a new page
					data = new_page();
				}
				tmp = (byte)(val >> 8*i);
				data[fPageIdx++] = tmp;
			}
		}		
	}

	public void writeShort(int val) throws IOException {
		if (fPageIdx+2 <= fPages.get(fPages.size()-1).length) {
			byte data[] = fPages.get(fPages.size()-1);
			byte tmp;
			
			tmp = (byte)(val >> 0);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 8);
			data[fPageIdx++] = tmp;
		} else {
			byte data[] = fPages.get(fPages.size()-1);
			byte tmp;
			
			for (int i=0; i<2; i++) {
				if (fPageIdx >= data.length) {
					// Add a new page
					data = new_page();
				}
				tmp = (byte)(val >> 8*i);
				data[fPageIdx++] = tmp;
			}
		}
	}
	
	private byte [] new_page() {
		byte tmp[] = new byte[PAGE_SIZE];
		fPages.add(tmp);
		fPageIdx = 0;
		
		return tmp;
	}
	
	public void writeBoolean(boolean arg0) throws IOException {
		throw new RuntimeException("writeBoolean not supported");
	}
	
	public void writeChars(String arg0) throws IOException {
		throw new RuntimeException("writeChars not supported");
	}
	
	public void writeChar(int arg0) throws IOException {
		throw new RuntimeException("writeChar not supported");
	}

	public void writeUTF(String arg0) throws IOException {
		throw new RuntimeException("writeUTF not supported");
	}

	public void writeDouble(double arg0) throws IOException {
		throw new RuntimeException("writeDouble not supported");
	}

	public void writeFloat(float arg0) throws IOException {
		throw new RuntimeException("writeFloat not supported");
	}
}

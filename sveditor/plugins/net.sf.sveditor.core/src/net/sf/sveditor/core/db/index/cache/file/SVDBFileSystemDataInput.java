package net.sf.sveditor.core.db.index.cache.file;

import java.io.DataInput;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class SVDBFileSystemDataInput implements DataInput {
	private List<byte[]>				fPages;
	private int							fPagesIdx;
	private int							fPageIdx;
	private int							fPageLimit;
	private int							fStartIdx = 0;
	public boolean						fDebugRead = false;
	
	public SVDBFileSystemDataInput() {
		fPages = new ArrayList<byte[]>();
	}
	
	public int byteAt(int idx) {
		idx += fStartIdx;
		int pages_idx;
		int page_idx;
		
		if (fPages.size() <= 1) {
			pages_idx = 0;
			page_idx = idx;
		} else {
			pages_idx = (idx / fPages.get(0).length);
			page_idx = (idx % fPages.get(0).length);
		}
		
		return fPages.get(pages_idx)[page_idx];
	}
	
	public int getOffset() {
		return (fPagesIdx*fPages.get(0).length)+fPageIdx;
	}
	
	public void setStartIdx(int idx) {
		fStartIdx = idx;
	}

	/**
	 * Finalizes the configuration for this data input
	 * 
	 * @param data_length
	 */
	public void finalize(int data_length) {
		// TODO:
//		fPageLimit = fPages.get(fPagesIdx).length;
	}
	
	public void reset() {
		fPagesIdx = 0;
		fPageIdx = 0;
	}
	
	public List<byte[]> getPages() {
		return fPages;
	}
	
	public int getPagesIdx() {
		return fPagesIdx;
	}
	
	public int getPageIdx() {
		return fPageIdx;
	}
	
	public int getLength() {
		int len = 0;
		for (int i=0; i<fPages.size(); i++) {
			len += fPages.get(i).length;
		}
		return (len-fStartIdx);
	}
	
	public void addPage(byte[] page) {
		if (fPages.size() == 0) {
			fPageLimit = page.length;
		}
		fPages.add(page);
	}
	
	public String readString() throws IOException {
		int len = readInt();
		byte tmp[] = new byte[len];
		readFully(tmp);
	
		String ret = new String(tmp);
		
		return ret;
	}

	public byte readByte() throws IOException {
		byte page[];
		
		if (fPageIdx >= fPageLimit) {
			page = new_page();
		} else {
			page = fPages.get(fPagesIdx);
		}
			
		byte ret = page[fPageIdx++];
		
		return ret;
	}

	public void readFully(byte[] b) throws IOException {
		readFully(b, 0, b.length);
	}

	public void readFully(byte[] b, int off, int len) throws IOException {
		byte data[] = fPages.get(fPagesIdx);
		
		int i=0;
		while (i < len) {
			if (fPageIdx >= fPageLimit) {
				data = new_page();
			}
			while (fPageIdx < fPageLimit && i<len) {
				b[off+i] = data[fPageIdx++];
				i++;
			}
		}
	}

	public int readInt() throws IOException {
		int ret = 0;
		int tmp;
		
		if (fPageIdx+4 <= fPageLimit) {
			byte page[] = fPages.get(fPagesIdx);
			
			// Full size available
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 24);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 16);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 8);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 0);
			
		} else {
			byte page[] = fPages.get(fPagesIdx);
			// Crosses a page boundary
			for (int i=0; i<4; i++) {
				if (fPageIdx >= fPageLimit) {
					page = new_page();
				}
				tmp = (page[fPageIdx++] & 0xFF);
				ret |= (tmp << 8*(3-i));
			}
		}
		
		return ret;
	}


	public long readLong() throws IOException {
		long ret = 0;
		long tmp;
		
		if (fPageIdx+8 <= fPageLimit) {
			byte page[] = fPages.get(fPagesIdx);
			
			// Full size available
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 56);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 48);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 40);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 32);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 24);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 16);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 8);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 0);
		} else {
			byte page[] = fPages.get(fPagesIdx);
			// Crosses a page boundary
			for (int i=0; i<8; i++) {
				if (fPageIdx >= fPageLimit) {
					page = new_page();
				}
				tmp = (page[fPageIdx++] & 0xFF);
				ret |= (tmp << 8*(7-i));
			}
		}
		
		return ret;
	}

	public short readShort() throws IOException {
		short ret = 0;
		int tmp;
		
		if (fPageIdx+2 <= fPageLimit) {
			byte page[] = fPages.get(fPagesIdx);
			
			// Full size available
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 8);
			tmp = (page[fPageIdx++] & 0xFF);
			ret |= (tmp << 0);
		} else {
			byte page[] = fPages.get(fPagesIdx);
			// Crosses a page boundary
			for (int i=0; i<2; i++) {
				if (fPageIdx >= fPageLimit) {
					page = new_page();
				}
				tmp = (page[fPageIdx++] & 0xFF);
				ret |= (tmp << 8*(1-i));
			}
		}
		
		return ret;
	}
	
	private byte [] new_page() {
		byte page[] = null;
	
		fPagesIdx++;
		page = fPages.get(fPagesIdx);
		fPageIdx = 0;
		fPageLimit = page.length;	
		
		return page;
	}
	
	public char readChar() throws IOException {
		throw new RuntimeException("readChar not supported");
	}
	
	public String readLine() throws IOException {
		throw new RuntimeException("readLine not supported");
	}

	public int readUnsignedByte() throws IOException {
		throw new RuntimeException("readUnsignedByte not supported");
	}

	public int readUnsignedShort() throws IOException {
		throw new RuntimeException("readUnsignedShort not supported");
	}

	public int skipBytes(int n) throws IOException {
		throw new RuntimeException("skipBytes not supported");
	}

	public double readDouble() throws IOException {
		throw new RuntimeException("readDouble not supported");
	}

	public float readFloat() throws IOException {
		throw new RuntimeException("readFloat not supported");
	}
	
	public String readUTF() throws IOException {
		throw new RuntimeException("readUTF not supported");
	}
	public boolean readBoolean() throws IOException {
		throw new RuntimeException("readBoolean not supported");
	}
}

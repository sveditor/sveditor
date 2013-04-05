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
	private byte							fTmp[];
	
	public SVDBFileSystemDataOutput() {
		fPages = new ArrayList<byte[]>();
		fPages.add(new byte[PAGE_SIZE]);
		fPageIdx = 0;
		fTmp = new byte[8];
	}
	
	
	public int getLength() {
		return (PAGE_SIZE * (fPages.size()-1)) + fPageIdx;
	}
	
	public byte[] getPage(int idx) {
		return fPages.get(idx);
	}

	public void write(int arg0) throws IOException {
		// TODO Auto-generated method stub

	}

	public void write(byte[] arg0) throws IOException {
		// TODO Auto-generated method stub

	}

	public void write(byte[] arg0, int arg1, int arg2) throws IOException {
		// TODO Auto-generated method stub

	}

	public void writeBoolean(boolean arg0) throws IOException {
		// TODO Auto-generated method stub

	}

	public void writeByte(int arg0) throws IOException {
		if (fPageIdx >= PAGE_SIZE) {
			fPages.add(new byte[PAGE_SIZE]);
			fPageIdx = 0;
		}
		fPages.get(fPages.size()-1)[fPageIdx] = (byte)arg0;
		fPageIdx++;
	}

	public void writeBytes(String arg0) throws IOException {
		// TODO Auto-generated method stub

	}

	public void writeChar(int arg0) throws IOException {
		// TODO Auto-generated method stub

	}

	public void writeChars(String arg0) throws IOException {
		// TODO Auto-generated method stub

	}

	public void writeInt(int val) throws IOException {
		if (fPageIdx+4 < fPages.get(fPages.size()-1).length) {
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
			
		}
	}

	public void writeLong(long arg0) throws IOException {
		// TODO Auto-generated method stub

	}

	public void writeShort(int arg0) throws IOException {
		// TODO Auto-generated method stub

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

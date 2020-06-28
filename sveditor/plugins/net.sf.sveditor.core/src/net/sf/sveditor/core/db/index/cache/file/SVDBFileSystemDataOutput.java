/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
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
	public boolean							fDebugWrite = false;
	
	public SVDBFileSystemDataOutput() {
		fPages = new ArrayList<byte[]>();
		fPages.add(new byte[PAGE_SIZE]);
		fPageIdx = 0;
	}
	
	
	public int getLength() {
		return (PAGE_SIZE * (fPages.size()-1)) + fPageIdx;
	}
	
	public int byteAt(int idx) {
		int pages_idx = (idx/PAGE_SIZE);
		int page_idx = (idx % PAGE_SIZE);
	
		return fPages.get(pages_idx)[page_idx];
	}
	
	public byte[] getPage(int idx) {
		return fPages.get(idx);
	}
	
	public List<byte[]> getPages() {
		return fPages;
	}
	
	public void write(int val) throws IOException {
		writeByte(val);
	}

	public void write(byte[] val) throws IOException {
		write(val, 0, val.length);
	}
	
	public int getOffset() {
		if (fPages.size() <= 1) {
			return fPageIdx;
		} else {
			return (PAGE_SIZE*(fPages.size()-1)) + fPageIdx;
		}
	}

	public void write(byte[] val, int off, int len) throws IOException {
		byte data[] = fPages.get(fPages.size()-1);
	
		int i=0;
		while (i < len) {
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
	
	public void writeString(String val) throws IOException {
		writeInt(val.length());
		writeBytes(val);
	}

	public void writeBytes(String val) throws IOException {
		byte data[] = fPages.get(fPages.size()-1);
		
		if (fPageIdx+val.length() <= data.length) {
			for (int i=0; i<val.length(); i++) {
				int v = val.charAt(i);
				data[fPageIdx++] = (byte)v;
			}
		} else {
			for (int i=0; i<val.length(); i++) {
				if (fPageIdx >= data.length) {
					data = new_page();
				}
				
				int v = val.charAt(i);
				data[fPageIdx++] = (byte)v;
			}
		}
	}

	public void writeInt(int val) throws IOException {
		
		byte data[] = fPages.get(fPages.size()-1);
		
		if (fPageIdx+4 <= data.length) {
			byte tmp;
			
			tmp = (byte)(val >> 24);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 16);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 8);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 0);
			data[fPageIdx++] = tmp;
		} else {
			byte tmp;
			
			for (int i=0; i<4; i++) {
				if (fPageIdx >= data.length) {
					// Add a new page
					data = new_page();
				}
				tmp = (byte)(val >> 8*(3-i));
				data[fPageIdx++] = tmp;
			}
		}
	}

	public void writeLong(long val) throws IOException {
		byte data[] = fPages.get(fPages.size()-1);
		
		if (fPageIdx+8 <= data.length) {
			byte tmp;
			
			tmp = (byte)(val >> 56);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 48);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 40);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 32);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 24);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 16);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 8);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 0);
			data[fPageIdx++] = tmp;
		} else {
			byte tmp;
			
			for (int i=0; i<8; i++) {
				if (fPageIdx >= data.length) {
					// Add a new page
					data = new_page();
				}
				tmp = (byte)(val >> 8*(7-i));
				data[fPageIdx++] = tmp;
			}
		}		
	}

	public void writeShort(int val) throws IOException {
		
		byte data[] = fPages.get(fPages.size()-1);
		if (fPageIdx+2 <= data.length) {
			byte tmp;
			
			tmp = (byte)(val >> 8);
			data[fPageIdx++] = tmp;
			tmp = (byte)(val >> 0);
			data[fPageIdx++] = tmp;
		} else {
			byte tmp;
			
			for (int i=0; i<2; i++) {
				if (fPageIdx >= data.length) {
					// Add a new page
					data = new_page();
				}
				tmp = (byte)(val >> 8*(1-i));
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

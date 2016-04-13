package net.sf.sveditor.core.db.index.external;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.zip.CRC32;

public class ExternalIndexerMsg {
	private byte				fBuf[];
	private int					fIdx;
	private int					fMax;
	private static final int	fIncr = 1024;
	
	public ExternalIndexerMsg() {
		fIdx = 0;
		fBuf = new byte[fIncr];
		fMax = fBuf.length;
	}

	// Setup for reading
	public void init_read() {
		fMax = fIdx;
		fIdx = 0;
	}
	
	public void init_write() {
		fIdx = 0;
		fMax = 0;
	}
	
	public void write32(int val) {
		if (fIdx+4 > fBuf.length) {
			resize(4);
		}
		write32(val, fBuf, fIdx);
		fIdx += 4;
	}
	
	private static void write32(int val, byte data[], int off) {
		data[off] = (byte)(val & 0xFF);
		data[off+1] = (byte)((val >> 8) & 0xFF);
		data[off+2] = (byte)((val >> 16) & 0xFF);
		data[off+3] = (byte)((val >> 24) & 0xFF);
	}
	
	public void write64(long val) {
		if (fIdx+8 > fBuf.length) {
			resize(8);
		}
		write64(val, fBuf, fIdx);
		fIdx += 8;
	}
	
	private static void write64(long val, byte data[], int off) {
		data[off] = (byte)(val & 0xFF);
		val >>= 8;
		data[off+1] = (byte)(val & 0xFF);
		val >>= 8;
		data[off+2] = (byte)(val & 0xFF);
		val >>= 8;
		data[off+3] = (byte)(val & 0xFF);
		val >>= 8;
		data[off+4] = (byte)(val & 0xFF);
		val >>= 8;
		data[off+5] = (byte)(val & 0xFF);
		val >>= 8;
		data[off+6] = (byte)(val & 0xFF);
		val >>= 8;
		data[off+7] = (byte)(val & 0xFF);
	}
	
	public int read32() {
		if (fIdx+4 > fMax) {
			return 0;
		}
		int ret = read32(fBuf, fIdx);
		fIdx += 4;
		return ret;
	}
	
	public long read64() {
		if (fIdx+8 > fMax) {
			return 0;
		}
		long ret = read64(fBuf, fIdx);
		fIdx += 8;
		return ret;
	}
	
	private static long read64(byte data[], int off) {
		long ret = (data[off+7] & 0xFF);
		ret <<= 8;
		ret |= (data[off+6] & 0xFF);
		ret <<= 8;
		ret |= (data[off+5] & 0xFF);
		ret <<= 8;
		ret |= (data[off+4] & 0xFF);
		ret <<= 8;
		ret |= (data[off+3] & 0xFF);
		ret <<= 8;
		ret |= (data[off+2] & 0xFF);
		ret <<= 8;
		ret |= (data[off+1] & 0xFF);
		ret <<= 8;
		ret |= (data[off] & 0xFF);
		
		return ret;		
	}
	
	private static int read32(byte data[], int off) {
		int ret = (data[off+3] & 0xFF);
		ret <<= 8;
		ret |= (data[off+2] & 0xFF);
		ret <<= 8;
		ret |= (data[off+1] & 0xFF);
		ret <<= 8;
		ret |= (data[off] & 0xFF);
		
		return ret;
	}
	
	public void write_str(String str) {
		int len = str.length();
		
		if (fIdx+len+4 > fBuf.length) {
			resize(len+4);
		}
	
		// String length
		write32(len, fBuf, fIdx);
		fIdx += 4;
	
		System.arraycopy(str.getBytes(), 0, fBuf, fIdx, len);
		fIdx += len;
	}
	
	public String read_str() {
		if (fIdx+4 > fMax){
			return null;
		}
		int len = read32(fBuf, fIdx);
		fIdx += 4;
	
		if (len == 0) {
			return "";
		}
		
		String ret = new String(fBuf, fIdx, len);
		fIdx += len;
		
		return ret;
	}
	
	private void resize(int incr) {
		if (fIdx+incr > fBuf.length) {
			byte tmp[] = fBuf;
			int new_sz = tmp.length + fIncr*((incr/fIncr)+1);
			fBuf = new byte[new_sz];
			System.arraycopy(tmp, 0, fBuf, 0, tmp.length);
			fMax = new_sz;
		}
	}
	
	public void send(OutputStream out) throws IOException {
		CRC32 crc = new CRC32();
		byte header[] = new byte[4+8];
	
		// Write size and header checksum
		write32(fIdx, header, 0);
	
		crc.reset();
		crc.update(header, 0, 4);
		write64(crc.getValue(), header, 4);
	
		// Send the header
		out.write(header, 0, header.length);
		
		// Send the body
		out.write(fBuf, 0, fIdx);
	
		// Compute and send the body checksum
		crc.reset();
		crc.update(fBuf, 0, fIdx);
		write64(crc.getValue(), header, 0);
		out.write(header, 0, 8);
	}

	public void recv(InputStream in) throws IOException {
		CRC32 crc = new CRC32();
		byte header[] = new byte[4+8];

		// Read the header first
		int sz = 0;
		do {
			sz += in.read(header, sz, (header.length-sz));
		} while (sz != header.length);
		
		// First, check to see if the header checksum is correct
		long exp_crc = read64(header, 4);
		crc.update(header, 0, 4);
		if (exp_crc != crc.getValue()) {
			throw new IOException("Bad header CRC: " + exp_crc + " vs " + crc.getValue());
		}
		
		// If it is, then proceed
		fIdx = 0;
		// Ensure sufficient space for data and CRC
		int len = read32(header, 0) + 8;
	
		resize(len); // ensure we have sufficient space
		sz = 0;
		
		do {
			sz += in.read(fBuf, sz, (len-sz));
		} while (sz != len);
		
		// Compute and check payload checksum
		exp_crc = read64(fBuf, len-8);
		crc.reset();
		crc.update(fBuf, 0, len-8);
		
		if (exp_crc != crc.getValue()) {
			throw new IOException("Bad payload CRC: " + exp_crc + " vs " + crc.getValue());
		}

		fMax = len-8;
	}
}

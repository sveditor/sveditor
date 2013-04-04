package net.sf.sveditor.core.db.index.cache.file;

import java.io.DataInput;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBFileSystem implements ILogLevelListener {
	private static final int			BLK_SIZE = 4096;
	private static final int			FILE_BLK_SIZE = (int)((1024L*1024L*1024L*4L)/BLK_SIZE);
//	private static final int			FILE_BLK_SIZE = (int)((1024L*1024L*4L)/BLK_SIZE);
	private static final int			ALLOC_PAGE_INCR = 1024;
	private LogHandle					fLog;
	private boolean						fDebugEn;
	private File						fDBDir;
	private byte						fUserData[];
	private byte						fAllocList[];
	private int							fFirstEmptyIdx;
	
	private List<RandomAccessFile>		fFileRWList;
	private int							fLastRwBlkLen;
	
	public SVDBFileSystem(File db_dir) {
		fLog = LogFactory.getLogHandle("SVDBFileSystem");
		fDebugEn = fLog.isEnabled();
		fLog.addLogLevelListener(this);
		
		fDBDir = db_dir;
		fFileRWList = new ArrayList<RandomAccessFile>();
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	/**
	 * 
	 * @return
	 */
	public boolean init() {
		boolean ret = true;
		
		// See if the DBDir exists
		if (!fDBDir.isDirectory()) {
			if (!fDBDir.mkdirs()) {
				fLog.error("Failed to create DB directory " + 
						fDBDir.getAbsolutePath());
			}
		}
		
		// Try to load the first file
		File f = new File(fDBDir, "1.db");
		
		if (!f.isFile()) {
			// Nothing here yet
			RandomAccessFile rw = null;
			try {
				rw = new RandomAccessFile(f, "rw");
			} catch (IOException e) {
				fLog.error("Failed to create first DB file " + 
						f.getAbsolutePath(), e);
			}
			fFileRWList.add(rw);
			fLastRwBlkLen = 0;
			fAllocList = new byte[ALLOC_PAGE_INCR];
		} else {
			RandomAccessFile rw = null;
			try {
				rw = new RandomAccessFile(f, "rw");
				fLastRwBlkLen = (int)(rw.length() / FILE_BLK_SIZE);
			} catch (IOException e) {
				fLog.error("Failed to create first DB file " + 
						f.getAbsolutePath(), e);
			}
			fFileRWList.add(rw);
			
			// TODO: read in the alloc list and initialize the AllocList
		}
	
		return ret;
	}
	
	public DataInput getUserData() {

		return null;
	}
	
	public void setUserData(SVDBFileSystemDataOutput data) {
		
	}

	public void sync() {
		
	}
	
	public synchronized void close() throws IOException {
		sync();
		
		for (RandomAccessFile rw : fFileRWList) {
			rw.close();
		}
	}
	
	public DataInput readFile(int id) {
		return null;
	}
	
	public int writeFile(SVDBFileSystemDataOutput data) throws IOException {
		int length = data.getLength();
	
		// Determine how many total blocks we need
		int avail_rootblock_bytes = 
				BLK_SIZE - 
				(
						4 + // file length
						4 + // additional-storage blocks
						0
				)
				;
		int reqd_blocks = 1;
		int remaining_size = length;

		while (remaining_size > avail_rootblock_bytes) {
			reqd_blocks++;
			avail_rootblock_bytes -= 4;
			remaining_size -= BLK_SIZE;
		}

		/*
		System.out.println("Size: " + length + " " + reqd_blocks + " " + 
				remaining_size + " " + avail_rootblock_bytes);
		 */
		
		int blocks[] = new int[reqd_blocks];
		for (int i=0; i<blocks.length; i++) {
			blocks[i] = allocBlock();
		}

		int blocks_idx = 0;
		byte block[] = new byte[BLK_SIZE];
		int idx = 0;
		
		// Write the first block
		idx = write32(idx, block, length);
		idx = write32(idx, block, (reqd_blocks-1));
		
		for (int i=1; i<blocks.length; i++) {
			idx = write32(idx, block, blocks[i]);
		}
		
		// TODO: may need to write multiple block-idx blocks
	
		int page_idx = 0, tmp_idx = 0;
		byte tmp[] = null;
		for (int i=0; i<length; i++) {
		
			if ((i % BLK_SIZE) == 0) {
				tmp = data.getPage(page_idx);
				tmp_idx = 0;
				if (i != 0) {
					page_idx++;
				}
			}
			
			block[idx] = tmp[tmp_idx];
			idx++;
			tmp_idx++;
			
			if (idx >= BLK_SIZE || i+1 >= length) {
				// reset the block
				writeBlock(blocks[blocks_idx], block);
				idx = 0;
				blocks_idx++;
			}
		}
		
		return blocks[0];
	}
	
	private static int write32(int idx, byte data[], int val) {
		byte tmp;
		int idx0 = idx;

		tmp = (byte)(val >> 0);
		data[idx++] = tmp;
		tmp = (byte)(val >> 8);
		data[idx++] = tmp;
		tmp = (byte)(val >> 16);
		data[idx++] = tmp;
		tmp = (byte)(val >> 24);
		data[idx++] = tmp;
	
		/*
		System.out.println("val=" + Integer.toHexString(val) + " " + 
				Integer.toHexString(data[idx0]) + " " + 
				Integer.toHexString(data[idx0+1]) + " " +
				Integer.toHexString(data[idx0+2]) + " " + 
				Integer.toHexString(data[idx0+3]));
		 */
	
		return idx;
	}

	public void deleteFile(int id) {
		
	}
	
	private byte [] readBlock(int id) throws IOException {
		int writer_id = (id / FILE_BLK_SIZE);
		int writer_blk_id = (id % FILE_BLK_SIZE);
		
		if (writer_id >= fFileRWList.size()) {
			return null;
		}
	
		RandomAccessFile rw = fFileRWList.get(writer_id);
		
		rw.seek(BLK_SIZE * writer_blk_id);
	
		return null;
	}
	
	public void writeBlock(int id, byte data[]) throws IOException {
		int writer_id = (id / FILE_BLK_SIZE);
		int writer_blk_id = (id % FILE_BLK_SIZE);
	
		// Backfill the writer array
		if (writer_id >= fFileRWList.size()) {
			// Add a new database file
			File f = new File(fDBDir, (writer_id+1) + ".db");
			RandomAccessFile rw = new RandomAccessFile(f, "rw");
			fFileRWList.add(rw);
			fLastRwBlkLen = 0;
		}
		
		RandomAccessFile rw = fFileRWList.get(writer_id);
		
		// See if the file is long enough
		if (writer_blk_id >= fLastRwBlkLen) {
			byte tmp[] = new byte[BLK_SIZE];
			
			// Extend the length
			rw.seek(fLastRwBlkLen*BLK_SIZE);
			while (writer_blk_id >= fLastRwBlkLen) {
				rw.write(tmp);
				fLastRwBlkLen++;
			}
		}
		
		// Finally, seek to the block offset and write the block
		rw.seek(writer_blk_id*BLK_SIZE);
		rw.write(data);
	}
	
	public synchronized int allocBlock() {
		int blk_id = -1;
		
		// First, see if we can find
		for (int i=fFirstEmptyIdx; i<fAllocList.length; i++) {
			if (fAllocList[i] != -1) {
				blk_id = 8*i;
				int mask = (int)fAllocList[i];
				for (int j=0; j<8; j++) {
					if ((mask & (1 << j)) == 0) {
						fAllocList[i] |= (1 << j);
						break;
					}
					blk_id++;
				}
				break;
			}
			fFirstEmptyIdx++;
		}
		
		if (fFirstEmptyIdx >= fAllocList.length) {
			// Need to allocate more space
			byte tmp[] = fAllocList;
			fAllocList = new byte[tmp.length + ALLOC_PAGE_INCR];
		
			for (int i=0; i<tmp.length; i++) {
				fAllocList[i] = tmp[i];
			}
			
			blk_id = 8*fFirstEmptyIdx;
			fAllocList[blk_id] |= 1;
		}
	
		return blk_id;
	}
	
	public synchronized void freeBlock(int id) {
		int alloc_idx = (id/8);
		if (alloc_idx < fFirstEmptyIdx) {
			fFirstEmptyIdx = alloc_idx;
		}
		int mask = ~(1 << (id & 7));
		fAllocList[alloc_idx] &= mask;
	}
}

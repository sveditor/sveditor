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
	private int							fAllocListFile;
	
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
	public synchronized boolean init() throws IOException {
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
		
		fLastRwBlkLen = 0;
		
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
			fAllocList = new byte[ALLOC_PAGE_INCR];
			
			// Reserve the first block
			fAllocList[0] = 1; 
			fAllocListFile = -1;
		} else {
			RandomAccessFile rw = null;
			
			rw = new RandomAccessFile(f, "rw");
			
			fFileRWList.add(rw);
			
			// Read the root block
			byte tmp[] = new byte[BLK_SIZE];
			readBlock(0, tmp);
			
			SVDBFileSystemDataInput in = new SVDBFileSystemDataInput();
			in.addPage(tmp);
			
			int n_files = in.readInt();
			fAllocListFile = in.readInt();
			int ud_len = in.readInt();
			
			if (ud_len == -1) {
				fUserData = null;
			} else {
				fUserData = new byte[ud_len];
				in.readFully(fUserData);
			}
			
			System.out.println("Sync: n_files=" + n_files);
			
			for (int i=2; i<=n_files; i++) {
				f = new File(fDBDir, i + ".db");
				rw = new RandomAccessFile(f, "rw");
				fFileRWList.add(rw);
			}
			
			// Now we can read in the alloc list and initialize the AllocList
			SVDBFileSystemDataInput alloc_in = readFile(fAllocListFile);
			int alloc_listlen = alloc_in.getLength();
			fAllocList = new byte[alloc_listlen];
			alloc_in.readFully(fAllocList);
		}
	
		return ret;
	}
	
	public DataInput getUserData() {
		if (fUserData != null) {
			return null;
		} else {
			SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
			ret.addPage(fUserData);
			return ret;
		}
	}
	
	public void setUserData(SVDBFileSystemDataOutput data) {
		if (data == null) {
			fUserData = null;
		} else {
			byte tdata[] = data.getPage(0);
			fUserData = new byte[tdata.length];
			// Only the first 2K is available for user data
			for (int i=0; (i<tdata.length && i<2048); i++) {
				fUserData[i] = tdata[i];
			}
		}
	}

	public synchronized void sync() throws IOException {
		SVDBFileSystemDataOutput alloc_out = new SVDBFileSystemDataOutput();
		// TODO: Create and save the root block
		SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
		
		// If we already have an alloc file, delete it
		if (fAllocListFile != -1) {
			deleteFile(fAllocListFile);
		}
		
		alloc_out.write(fAllocList);
		fAllocListFile = writeFile(alloc_out);
		
		/**
		 * Root block is:
		 * - Number of files in this filesystem
		 * - Handle to the alloc list
		 * - user data length
		 * - user data
		 */
		out.writeInt(fFileRWList.size());
		out.writeInt(fAllocListFile);
		if (fUserData != null) {
			out.writeInt(fUserData.length);
			out.write(fUserData);
		} else {
			out.writeInt(-1);
		}

		// Write back the root block
		writeBlock(0, out.getPage(0));
	}
	
	public synchronized void close() throws IOException {
		sync();
		
		for (RandomAccessFile rw : fFileRWList) {
			rw.close();
		}
	}
	
	public SVDBFileSystemDataInput readFile(int id) throws IOException {
		SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
		byte tmp[] = new byte[BLK_SIZE];
	
		// Read root block
		readBlock(id, tmp);
		ret.addPage(tmp);
		
		int length  = ret.readInt(); // Total length of the file
		int nblocks = ret.readInt(); // Number of non-root blocks
		
		// Read in the remaining root and storage blocks
		for (int i=0; i<nblocks; i++) {
			int block_id = ret.readInt();
			tmp = new byte[BLK_SIZE];
			readBlock(block_id, tmp);
			ret.addPage(tmp);
		}
		
		ret.finalize(length);
		
		return ret;
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
		int last_rootblk_idx = 0;

		while (remaining_size > avail_rootblock_bytes) {
			reqd_blocks++;
			avail_rootblock_bytes -= 4;
			if (avail_rootblock_bytes <= 0) {
				avail_rootblock_bytes = BLK_SIZE;
				last_rootblk_idx++;
				// Need an additional root block
				reqd_blocks++;
			}
			remaining_size -= BLK_SIZE;
		}
		
		int blocks[] = new int[reqd_blocks];
		for (int i=0; i<blocks.length; i++) {
			blocks[i] = allocBlock();
		}

		int blocks_idx = 0;
		byte block[] = new byte[BLK_SIZE];
		int idx = 0;
		
		// Fill in the base root block
		idx = write32(idx, block, length);
		idx = write32(idx, block, (reqd_blocks-1));
	
		// Add the additional-block pointers
		for (int i=1; i<blocks.length; i++) {
			idx = write32(idx, block, blocks[i]);
			
			if (idx >= BLK_SIZE) {
				// write back the block and move on to the next
				writeBlock(blocks[blocks_idx], block);
				blocks_idx++;
				idx = 0;
			}
		}
		
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
//		int idx0 = idx;

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

	public void deleteFile(int id) throws IOException {
		SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
		byte tmp[] = new byte[BLK_SIZE];
	
		// Read root block
		readBlock(id, tmp);
		ret.addPage(tmp);
		
		/* int length  = */ ret.readInt(); // Total length of the file
		int nblocks = ret.readInt(); // Number of non-root blocks
		int blocks[] = new int[nblocks+1];
		blocks[0] = id;
		int blocks_to_read = computeRootBlockCount(nblocks);
		
		// Read in the remaining block ids and free them
		for (int i=0; i<nblocks; i++) {
			int block_id = ret.readInt();
			if (i < blocks_to_read) {
				tmp = new byte[BLK_SIZE];
				readBlock(block_id, tmp);
				ret.addPage(tmp);
			}
			freeBlock(block_id);
		}		
		
		freeBlock(id);
	}
	
	/**
	 * Computes the number of root blocks that must be read
	 * given the number of non-root blocks required
	 * 
	 * @param nblocks
	 * @return
	 */
	private static int computeRootBlockCount(int nblocks) {
		int first_rootblk_blk_pointers = (BLK_SIZE -
				(
						4 + // length
						4 + // nblocks
						0
				)) / 4;
		if (nblocks > first_rootblk_blk_pointers) {
			nblocks -= first_rootblk_blk_pointers;
			return ((nblocks-1) / (BLK_SIZE/4)) + 1;
		} else {
			return 0;
		}
	}
	
	private void readBlock(int id, byte data[]) throws IOException {
		int writer_id = (id / FILE_BLK_SIZE);
		int writer_blk_id = (id % FILE_BLK_SIZE);
		
		if (writer_id >= fFileRWList.size()) {
			return;
		}
	
		RandomAccessFile rw = fFileRWList.get(writer_id);
		
		rw.seek(BLK_SIZE * writer_blk_id);

		rw.read(data, 0, BLK_SIZE);
	}
	
	private void writeBlock(int id, byte data[]) throws IOException {
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

	/**
	 * Allocate a filesystem block
	 * 
	 * @return
	 */
	private synchronized int allocBlock() {
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
			
			fAllocList[fFirstEmptyIdx] |= 1;
			blk_id = 8*fFirstEmptyIdx;
		}
	
		return blk_id;
	}
	
	/**
	 * Free a filesystem block
	 * @param id
	 */
	private synchronized void freeBlock(int id) {
		int alloc_idx = (id/8);
		if (alloc_idx < fFirstEmptyIdx) {
			fFirstEmptyIdx = alloc_idx;
		}
		int mask = ~(1 << (id & 7));
		fAllocList[alloc_idx] &= mask;
	}

}

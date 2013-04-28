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
	private String						fVersion;
	private LogHandle					fLog;
	private boolean						fDebugEn = false;
	private File						fDBDir;
	private byte						fUserData[];
	
	private byte						fAllocList[];
	private int							fFirstEmptyIdx;
	private int							fAllocListFile;
	
	private List<RandomAccessFile>		fFileRWList;
	private int							fLastRwBlkLen;
	
	public SVDBFileSystem(File db_dir, String version) {
		fDBDir = db_dir;
		fVersion = version;
		
		fLog = LogFactory.getLogHandle("SVDBFileSystem");
		fDebugEn = fLog.isEnabled();
		fLog.addLogLevelListener(this);
		
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
			// Initialize the filesystem
			initialize();
			ret = false;
		} else {
			// Filesystem storage exists. See if we can open it
			try {
				ret = open_filesystem(f);
			} catch (IOException e) {
				// Failed to open filesystem
				ret = false;
				cleanup();
				initialize();
			} catch (Exception e) {
				// Failed to open filesystem
				ret = false;
				cleanup();
				initialize();
			}
		}
	
		return ret;
	}
	
	private void initialize() {
		File f = new File(fDBDir, "1.db");
		
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
		fFirstEmptyIdx = 0;
		fLastRwBlkLen = 0;
	}
	
	private boolean open_filesystem(File f) throws IOException {
		boolean ret = true;
		RandomAccessFile rw = null;
		
		rw = new RandomAccessFile(f, "rw");
		
		fFileRWList.add(rw);
		
		// Read the root block
		byte tmp[] = new byte[BLK_SIZE];
		readBlock("rootFile", 0, tmp);
		
		SVDBFileSystemDataInput in = new SVDBFileSystemDataInput();
		in.addPage(tmp);

		/**
		 * Root block is:
		 * - Filesystem version-string length
		 * - Filesystem version (string)
		 * - Number of storage files in this filesystem
		 * - Block length of the last file
		 * - Handle to the alloc list
		 * - Alloc list length
		 * - user data length
		 * - user data
		 */
		String version = in.readString();
		
		if (!fVersion.equals(version)) {
			// Version doesn't match, so re-initialize the filesystem
			ret = false;
			cleanup();
			initialize();
		} else {
			int n_files = in.readInt();
			fLastRwBlkLen  = in.readInt();
			fAllocListFile = in.readInt();
			int alloc_list_len = in.readInt();
			int ud_len = in.readInt();
			
			if (ud_len == -1) {
				fUserData = null;
			} else {
				fUserData = new byte[ud_len];
				in.readFully(fUserData);
			}

			for (int i=2; i<=n_files; i++) {
				f = new File(fDBDir, i + ".db");
				rw = new RandomAccessFile(f, "rw");
				fFileRWList.add(rw);
			}

			// Now we can read in the alloc list and initialize the AllocList
			SVDBFileSystemDataInput alloc_in = readFile("allocList", fAllocListFile);
			fAllocList = new byte[alloc_list_len];
			alloc_in.readFully(fAllocList);
		}
		
		return ret;
	}
	
	private void cleanup() {
		fFileRWList.clear();
		
		File files[] = fDBDir.listFiles();
		if (files != null) {
			for (File f : files) {
				if (f.getName().endsWith(".db")) {
					if (!f.delete()) {
						fLog.error("Failed to delete storage for " + f.getAbsolutePath());
					}
				}
			}
		}
	}
	
	public SVDBFileSystemDataInput getUserData() {
		if (fUserData == null) {
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
			int ud_size = (data.getLength() < 2048)?data.getLength():2048;
//			int ud_size = 2048;
			byte tdata[] = data.getPage(0);
			fUserData = new byte[ud_size];
			// Only the first 2K is available for user data
			for (int i=0; (i<ud_size && i < tdata.length); i++) {
				fUserData[i] = tdata[i];
			}
		}
	}

	public synchronized void sync() throws IOException {
		SVDBFileSystemDataOutput alloc_out = new SVDBFileSystemDataOutput();
		// Create and save the root block
		SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
		
		// If we already have an alloc file, delete it
		if (fAllocListFile != -1) {
			deleteFile("allocList", fAllocListFile);
		}
		
		alloc_out.write(fAllocList);
		fAllocListFile = writeFile("allocList", alloc_out);
		
		/**
		 * Root block is:
		 * - Filesystem version-string length
		 * - Filesystem version (string)
		 * - Number of storage files in this filesystem
		 * - Block length of the last file
		 * - Handle to the alloc list
		 * - Alloc list length
		 * - user data length
		 * - user data
		 */
		out.writeString(fVersion);
		
		out.writeInt(fFileRWList.size());
		out.writeInt(fLastRwBlkLen);
		out.writeInt(fAllocListFile);
		out.writeInt(fAllocList.length);
		if (fUserData != null) {
			out.writeInt(fUserData.length);
			out.write(fUserData);
		} else {
			out.writeInt(-1);
		}

		// Write back the root block
		writeBlock("rootFile", 0, out.getPage(0));
	}
	
	public synchronized void close() throws IOException {
		sync();
		
		for (RandomAccessFile rw : fFileRWList) {
			rw.close();
		}
	}
	
	public SVDBFileSystemDataInput readFile(String path, int id) throws IOException {
		SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
		byte tmp[] = new byte[BLK_SIZE];
		int total_blocks=0;
		
		// Read root block
		readBlock(path, id, tmp);
		ret.addPage(tmp);
		total_blocks++;
		
		int length  = ret.readInt(); // Total length of the file
		int nblocks = ret.readInt(); // Number of non-root blocks
		
		// Read in the remaining root and storage blocks
		for (int i=0; i<nblocks; i++) {
			int block_id = ret.readInt();
			tmp = new byte[BLK_SIZE];
			readBlock(path, block_id, tmp);
			ret.addPage(tmp);
			total_blocks++;
		}
		int start_idx = ret.getOffset();
		ret.setStartIdx(start_idx);
	
		// Compute the initial page and page offset
		ret.finalize(length);
		
		return ret;
	}
	
	public int writeFile(String path, SVDBFileSystemDataOutput data) throws IOException {
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
				writeBlock(path, blocks[blocks_idx], block);
				blocks_idx++;
				idx = 0;
			}
		}
		
		int page_idx = 0, tmp_idx = 0;
		byte tmp[] = data.getPage(page_idx);
		for (int i=0; i<length; i++) {

			if (tmp_idx >= tmp.length) {
				page_idx++;
				tmp = data.getPage(page_idx);
				tmp_idx = 0;
			}
			
			block[idx] = tmp[tmp_idx];
			idx++;
			tmp_idx++;
			
			if (idx >= BLK_SIZE || i+1 >= length) {
				// reset the block
				writeBlock(path, blocks[blocks_idx], block);
				idx = 0;
				blocks_idx++;
			}
		}

		return blocks[0];
	}
	
	private static int write32(int idx, byte data[], int val) {
		byte tmp;

		tmp = (byte)(val >> 24);
		data[idx++] = tmp;
		tmp = (byte)(val >> 16);
		data[idx++] = tmp;
		tmp = (byte)(val >> 8);
		data[idx++] = tmp;
		tmp = (byte)(val >> 0);
		data[idx++] = tmp;
	
		return idx;
	}

	public void deleteFile(String path, int id) throws IOException {
		SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
		byte tmp[] = new byte[BLK_SIZE];
		
		if (id < 1) {
			throw new IOException("Cannot delete root block");
		}
	
		// Read root block
		readBlock(path, id, tmp);
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
				readBlock(path, block_id, tmp);
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
	
	private void readBlock(String path, int id, byte data[]) throws IOException {
		int writer_id = (id / FILE_BLK_SIZE);
		int writer_blk_id = (id % FILE_BLK_SIZE);
		
		if (writer_id >= fFileRWList.size()) {
			throw new IOException("writer_id " + writer_id + " out of range; id=" + id + " size is " + fFileRWList.size());
		}
	
		RandomAccessFile rw = fFileRWList.get(writer_id);
		
		rw.seek(BLK_SIZE * writer_blk_id);

		rw.read(data, 0, BLK_SIZE);
	}
	
	private void writeBlock(String path, int id, byte data[]) throws IOException {
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

package net.sf.sveditor.core.db.index.cache.file;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBFileSystem implements ILogLevelListener {
	private static final int			VALID_MAGIC_NUMBER = 0xA5A5EAEA;
	
	
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
	private boolean						fIsOpen;
	private Exception					fCloseStack;
	
	private class FileInfo {
		public int					fFileId;
		public List<Integer>		fBlockIdList = new ArrayList<Integer>();
	}

	private List<FileInfo>				fFileList;
	private boolean						fTrackFiles = false;
	private int							fFileInfoHndl;
	
	public SVDBFileSystem(File db_dir, String version) {
		fDBDir = db_dir;
		fVersion = version;
		
		fLog = LogFactory.getLogHandle("SVDBFileSystem");
		fDebugEn = fLog.isEnabled();
		fLog.addLogLevelListener(this);
		
		fFileRWList = new ArrayList<RandomAccessFile>();
		fFileList = new ArrayList<SVDBFileSystem.FileInfo>();
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
			} catch (Exception e) {
				// Failed to open filesystem
				ret = false;
			}
			
			if (!ret) {
				cleanup();
				initialize();
			}
		}
		
		fIsOpen = true;
	
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
		fFileInfoHndl = -1;
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
		 * - Magic number
		 * - Filesystem version-string length
		 * - Filesystem version (string)
		 * - Number of storage files in this filesystem
		 * - Block length of the last file
		 * - Handle to the alloc list
		 * - Alloc list length
		 * - Handle to the file-info list
		 * - File-info list length
		 * - user data length
		 * - user data
		 */
		int magic_number = in.readInt();
		
		if (magic_number != VALID_MAGIC_NUMBER) {
			ret = false;
		} else {
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
				
				// Read back the file list;
				fFileInfoHndl = in.readInt();
				int file_list_size = in.readInt();

				if (fTrackFiles) {
					fTrackFiles = false;
					SVDBFileSystemDataInput file_info_in = readFile("fileInfo", fFileInfoHndl);
					fTrackFiles = true;

					fFileList.clear();
					for (int i=0; i<file_list_size; i++) {
						FileInfo info = new FileInfo();
						info.fFileId = file_info_in.readInt();
						int n_blocks = file_info_in.readInt();
						for (int j=0; j<n_blocks; j++) {
							info.fBlockIdList.add(file_info_in.readInt());
						}
						fFileList.add(info);
					}

				}

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
				boolean track_files = fTrackFiles;
				fTrackFiles = false;
				SVDBFileSystemDataInput alloc_in = readFile("allocList", fAllocListFile);
				fTrackFiles = track_files;
				fAllocList = new byte[alloc_list_len];
				alloc_in.readFully(fAllocList);

				if (fTrackFiles) {
					for (int i=0; i<fAllocList.length; i++) {
						if ((i % 16) == 0) {
							if (i != 0) {
								System.out.println();
							}
							System.out.print("" + i + ": ");
						}
						System.out.print(Integer.toHexString(fAllocList[i]) + " ");
					}
					System.out.println();

					System.out.println("--> Validate Initial Load alloc_list_len=" + alloc_list_len);
					removeFileInfo(null);
					System.out.println("<-- Validate Initial Load");
				}
			}
		}
		
		if (ret) {
			// Mark the filesystem as open and invalid. This enables us to 
			// detect filesystem invalidity due to improper close
			write32(0, tmp, ~VALID_MAGIC_NUMBER);
			writeBlock("rootBlock", 0, tmp);
		}
		
		return ret;
	}
	
	private void cleanup() {
		// Close any open files we have sitting around...
		for (RandomAccessFile rw : fFileRWList) {
			try {
				rw.close();
			} catch (IOException e) {}
		}
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
	
	public synchronized int blockSize() {
		int size = 0;
		
		for (int i=0; i<fAllocList.length; i++) {
			byte mask = fAllocList[i];
			
			for (int j=0; j<8; j++) {
				if ((mask & (1 << j)) != 0) {
					size++;
				}
			}
		}
		
		return size;
	}
	
	public synchronized SVDBFileSystemDataInput getUserData() {
		if (fUserData == null) {
			return null;
		} else {
			SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
			ret.addPage(fUserData);
			return ret;
		}
	}
	
	public synchronized void setUserData(SVDBFileSystemDataOutput data) {
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
		
		if (!fIsOpen) {
			if (fCloseStack != null) {
				fCloseStack.printStackTrace();
			}
			throw new IOException("Filesystem is closed");
		}
		// Create and save the root block
		SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();

		if (fTrackFiles && fFileInfoHndl != -1) {
			fTrackFiles = false;
			deleteFile("fileInfo",  fFileInfoHndl);
			fTrackFiles = true;
		}

		// Write back the list of files
		if (fTrackFiles) {
			SVDBFileSystemDataOutput file_info_out = new SVDBFileSystemDataOutput();
			for (FileInfo info : fFileList) {
				file_info_out.writeInt(info.fFileId);
				file_info_out.writeInt(info.fBlockIdList.size());
				for (int j=0; j<info.fBlockIdList.size(); j++) {
					file_info_out.writeInt(info.fBlockIdList.get(j));
				}
			}
		
			// Need to ensure this doesn't end up in the info list
			fTrackFiles = false;
			fFileInfoHndl = writeFile("fileInfo", file_info_out);
			fTrackFiles = true;
		}
		
		/**
		 * Root block is:
		 * - Magic number
		 * - Filesystem version-string length
		 * - Filesystem version (string)
		 * - Number of storage files in this filesystem
		 * - Block length of the last file
		 * - Handle to the alloc list
		 * - Alloc list length
		 * - Handle to the file info file
		 * - Length of the file info list
		 * - user data length
		 * - user data
		 */
		out.writeInt(VALID_MAGIC_NUMBER);
		out.writeString(fVersion);
		
		out.writeInt(fFileRWList.size());
		out.writeInt(fLastRwBlkLen);
		
		// Write back the allocation table
		writeAllocList();
		out.writeInt(fAllocListFile);
		out.writeInt(fAllocList.length);
		
		if (fTrackFiles) {
			out.writeInt(fFileInfoHndl);
			out.writeInt(fFileList.size());
		} else {
			// Not tracking files
			out.writeInt(-1);
			out.writeInt(0);
		}
		
		if (fUserData != null) {
			out.writeInt(fUserData.length);
			out.write(fUserData);
		} else {
			out.writeInt(-1);
		}
	

		// Write back the root block
		writeBlock("rootFile", 0, out.getPage(0));
	}
	
	public synchronized void delete() throws IOException {
		close();
	
		SVFileUtils.delete(fDBDir);
	}
	
	public synchronized void close() throws IOException {
		sync();
		
		for (RandomAccessFile rw : fFileRWList) {
			rw.close();
		}
		fFileRWList.clear();
		
		fIsOpen = false;
		try {
			throw new Exception();
		} catch (Exception e) {
			fCloseStack = e;
		}
	}
	
	public synchronized SVDBFileSystemDataInput readFile(String path, int id) throws IOException {
		SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
		byte tmp[] = new byte[BLK_SIZE];
		FileInfo info = null;
		
		// Read root block
		readBlock(path, id, tmp);
		ret.addPage(tmp);
		
		int length  = ret.readInt(); // Total length of the file
		int nblocks = ret.readInt(); // Number of non-root blocks
		
		if (fTrackFiles) {
			info = findFileInfo(id);
			
			if (info == null) {
				System.out.println("readFile: failed to find id=" + id + " " + path);
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
			
			if (info != null && nblocks != info.fBlockIdList.size()) {
				System.out.println("readFile: block count wrong for " + id + " " + path + 
						" nblocks=" + nblocks + " actual=" + info.fBlockIdList.size());
			}
		}
		
		// Read in the remaining root and storage blocks
		for (int i=0; i<nblocks; i++) {
			int block_id = ret.readInt();
			
			if (fTrackFiles && info != null) {
				if (block_id != info.fBlockIdList.get(i)) {
					System.out.println("readFile: block id " + i + " wrong for " + id + " " + path + 
							" block_id=" + block_id + " actual=" + info.fBlockIdList.get(i));
				}
			}
			tmp = new byte[BLK_SIZE];
			readBlock(path, block_id, tmp);
			ret.addPage(tmp);
		}
		int start_idx = ret.getOffset();
		ret.setStartIdx(start_idx);
	
		// Compute the initial page and page offset
		ret.finalize(length);
		
		return ret;
	}
	
	public synchronized int writeFile(String path, SVDBFileSystemDataOutput data) throws IOException {
		FileInfo info = null;
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
			if (avail_rootblock_bytes <= 0) {
				avail_rootblock_bytes = BLK_SIZE;
				// Need an additional root block
				reqd_blocks++;
			}
			remaining_size -= BLK_SIZE;
		}
		
		if (fTrackFiles) {
			info = new FileInfo();
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
	
		if (fTrackFiles) {
			for (int i=0; i<blocks.length; i++) {
				if (fTrackFiles) {
					if (i==0) {
						info.fFileId = blocks[i];
					} else {
						info.fBlockIdList.add(blocks[i]);
					}
				}
			}
			
			validateBlocksUnique(info);
			
			fFileList.add(info);
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

	public synchronized void deleteFile(String path, int id) throws IOException {
		FileInfo info = null;
		SVDBFileSystemDataInput ret = new SVDBFileSystemDataInput();
		byte tmp[] = new byte[BLK_SIZE];
		
		if (id < 1) {
			throw new IOException("Cannot delete root block");
		}
	
		if (fTrackFiles) {
			info = findFileInfo(id);
			
			if (info == null) {
				System.out.println("deleteFile: failed to find " + id + " " + path);
			}
		
			removeFileInfo(info);
		}
	
		// Read root block
		readBlock(path, id, tmp);
		ret.addPage(tmp);
		
		/* int length  = */ ret.readInt(); // Total length of the file
		int nblocks = ret.readInt(); // Number of non-root blocks
		if (nblocks < 0) {
			
		}
		int blocks_to_read = computeRootBlockCount(nblocks);
		
		if (fTrackFiles && info != null) {
			if (nblocks != info.fBlockIdList.size()) {
				System.out.println("deleteFile: mismatch in blocks for " + id + 
						" " + path + " nblocks=" + nblocks + " actual=" +
						info.fBlockIdList.size());
			}
		}
		
		// Read in the remaining block ids and free them
		for (int i=0; i<nblocks; i++) {
			int block_id = ret.readInt();
			
			if (fTrackFiles && info != null) {
				if (block_id != info.fBlockIdList.get(i)) {
					System.out.println("deleteFile: block " + i + " mismatch " +
							"block_id=" + block_id + " actual=" +
							info.fBlockIdList.get(i));
				}
			}
			
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
	 * writeAllocList
	 * 
	 * Writing the allocation table back is a bit tricky, since it 
	 * involves simultaneously allocating new blocks and writing
	 * the allocation table
	 */
	private int writeAllocList() throws IOException {
		// If we already have an alloc file, delete it
		if (fAllocListFile != -1) {
			boolean track_files = fTrackFiles;
			fTrackFiles = false;
			deleteFile("allocList", fAllocListFile);
			fTrackFiles = track_files;
		}
		
		// Ask for enough space such that we could fully 
		// allocate the full new space
		int length = fAllocList.length+(fAllocList.length/8)+2;
		
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
			if (avail_rootblock_bytes <= 0) {
				avail_rootblock_bytes = BLK_SIZE;
				// Need an additional root block
				reqd_blocks++;
			}
			remaining_size -= BLK_SIZE;
		}
		
		int blocks[] = new int[reqd_blocks+1];
		
		for (int i=0; i<blocks.length; i++) {
			blocks[i] = allocBlock();
		}
		
		if (fTrackFiles) {
			for (int i=0; i<fAllocList.length; i++) {
				if ((i % 16) == 0) {
					if (i != 0) {
						System.out.println();
					}
					System.out.print("" + i + ": ");
				}
				System.out.print(Integer.toHexString(fAllocList[i]) + " ");
			}
			System.out.println();
		}
	
		int blocks_idx = 0;
		byte block[] = new byte[BLK_SIZE];
		int idx = 0;
		
		idx = write32(idx, block, fAllocList.length);
		idx = write32(idx, block, (reqd_blocks));

		for (int i=1; i<blocks.length; i++) {
			idx = write32(idx, block, blocks[i]);
			
			if (idx >= BLK_SIZE) {
				// write back the block and move on to the next
				writeBlock("alloc file", blocks[blocks_idx], block);
				blocks_idx++;
				idx = 0;
			}
		}
		
//		System.out.println("writeAllocList: fAllocList.length=" + fAllocList.length + " blocks.length=" + blocks.length + " idx=" + idx);
		
		for (int i=0; i<fAllocList.length; i++) {
			block[idx] = fAllocList[i];
			idx++;
		
			if (idx >= BLK_SIZE || i+1 >= fAllocList.length) {
				if (blocks_idx >= blocks.length) {
					System.out.println("blocks_idx=" + blocks_idx + " blocks.length=" + blocks.length + " i=" + i + " length=" + fAllocList.length);
				}
				writeBlock("alloc file", blocks[blocks_idx], block);
				idx = 0;
				// Zero out the block
				for (int j=0; j<BLK_SIZE; j++) {
					block[j] = 0;
				}
				blocks_idx++;
			}
		}
		
		fAllocListFile = blocks[0];

		return fAllocList.length;
	}
	
	private FileInfo findFileInfo(int id) {
		for (FileInfo info : fFileList) {
			if (info.fFileId == id) {
				return info;
			}
		}
		return null;
	}
	
	private void validateBlocksUnique(FileInfo info) {
		boolean err = false;
		for (FileInfo i : fFileList) {
			if (info.fFileId == i.fFileId ||
					i.fBlockIdList.contains(info.fFileId)) {
				System.out.println("validateBlocksUnique: id=" + info.fFileId + " already in use");
				err = true;
			}
			
			for (int block_id : info.fBlockIdList) {
				if (block_id == i.fFileId ||
						i.fBlockIdList.contains(block_id)) {
					System.out.println("validateBlocksUnique: id=" + info.fFileId + " already in use");
					err = true;
				}
			}
		}
		
		if (err) {
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}
	
	private void removeFileInfo(FileInfo info) {
		for (FileInfo i : fFileList) {
			if (!blockAllocated(i.fFileId)) {
				System.out.println("removeFileInfo: block " + i.fFileId + " marked as free");
			}
			
			for (int block_id : i.fBlockIdList) {
				if (!blockAllocated(block_id)) {
					System.out.println("removeFileInfo: block " + block_id + " marked as free");
				}
			}
		}
		
		if (info != null) {
			fFileList.remove(info);
		}
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
						if (blockAllocated(blk_id)) {
							System.out.println("allocBlock(1): blk_id " + blk_id + " already allocated");
						}
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
			if (blockAllocated(blk_id)) {
				System.out.println("allocBlock(2): blk_id " + blk_id + " already allocated");
			}
			
			fAllocList[fFirstEmptyIdx] |= 1;
		}
		
		if (!blockAllocated(blk_id)) {
			System.out.println("allocBlock: blk_id " + blk_id + " not actually allocated");
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
	
	private synchronized boolean blockAllocated(int id) {
		int alloc_idx = (id/8);
		int mask = (1 << (id & 7));
		return ((fAllocList[alloc_idx] & mask) != 0);
	}

}

package net.sf.sveditor.core.db.index.cache;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;

public class SVDBFileFSRootBlock {
	private long				fBlockSize;
	private long				fDirentPtr;
	private long				fBitmapPtr;
	
	public SVDBFileFSRootBlock(DataInput in) throws IOException {
		fBlockSize = in.readLong();
		fDirentPtr = in.readLong();
		fBitmapPtr = in.readLong();
		
	}
	
	public void sync(DataOutput out) throws IOException {
		out.writeLong(fBlockSize);
		out.writeLong(fDirentPtr);
		out.writeLong(fBitmapPtr);
	}
	
}

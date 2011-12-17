/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


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

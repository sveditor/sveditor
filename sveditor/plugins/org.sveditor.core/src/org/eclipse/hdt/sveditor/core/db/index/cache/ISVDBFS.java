/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.index.cache;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.RandomAccessFile;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBFS {
	
	String getRoot();
	
	/**
	 * The FS provider must remove the path corresponding to itself
	 * from the supplied list. This is used by the database-compacting
	 * process
	 * 
	 * @param db_file_list
	 */
	void removeStoragePath(List<File> db_file_list);
	
	InputStream openFileRead(String path) throws IOException;
	
	RandomAccessFile openChannelRead(String path);
	
	DataInput openDataInput(String path);
	
	void closeChannel(RandomAccessFile ch);
	
	void close(InputStream in);
	
	void closeInput(DataInput in);
	
	OutputStream openFileWrite(String path);
	
	RandomAccessFile openChannelWrite(String path);
	
	DataOutput openDataOutput(String path);
	
	void closeOutput(DataOutput out);
	
	boolean fileExists(String path);
	
	long lastModified(String path);
	
	void delete(IProgressMonitor monitor, String path);
	
	void mkdirs(String path);
	
	void sync() throws IOException;

}

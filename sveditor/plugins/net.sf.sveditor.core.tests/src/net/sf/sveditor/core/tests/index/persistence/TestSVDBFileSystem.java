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
package net.sf.sveditor.core.tests.index.persistence;

import java.io.File;
import java.io.IOException;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystemDataInput;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystemDataOutput;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestSVDBFileSystem extends SVCoreTestCaseBase {

	/**
	 * Tests that we can:
	 * - write a file to the filesystem
	 * - close the filesystem
	 * - reopen the filesystem
	 * - read back the file
	 */
	public void testInitOpen() throws IOException {
		File fs_dir = new File(fTmpDir, "fs_dir");
		
		SVDBFileSystem fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());

		boolean is_valid = fs.init();
	
		// We expect the filesystem to not be valid
		assertFalse(is_valid);
		
		// Now, write a file
		SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
		out.writeString("Hello World");
		
		int fileid = fs.writeFile("", out);
		
		// Now, close the filesystem
		fs.close();
		
		// Re-create and re-initialize the filesystem
		fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());
		
		is_valid = fs.init();
		
		assertTrue(is_valid);
		
		SVDBFileSystemDataInput in = fs.readFile("", fileid);
		
		assertNotNull(in);
		
		String str = in.readString();
		assertEquals("Hello World", str);
		
		fs.close();
	}

	/**
	 * Tests that we correctly identify a filesystem of
	 * a different version
	 */
	public void testInitOpenDifferentVersion() throws IOException {
		File fs_dir = new File(fTmpDir, "fs_dir");
		
		SVDBFileSystem fs = new SVDBFileSystem(fs_dir, SVCorePlugin.getVersion());

		boolean is_valid = fs.init();
	
		// We expect the filesystem to not be valid
		assertFalse(is_valid);
		
		// Now, write a file
		SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
		out.writeString("Hello World");
		
		int fileid = fs.writeFile("", out);
		
		// Now, close the filesystem
		fs.close();
		
		// Re-create and re-initialize the filesystem
		fs = new SVDBFileSystem(fs_dir, "0.0.0");
		
		is_valid = fs.init();
		
		assertFalse(is_valid);
		
		fs.close();
	}
}

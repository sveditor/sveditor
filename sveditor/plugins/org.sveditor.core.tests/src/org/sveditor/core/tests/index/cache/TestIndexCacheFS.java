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
package org.sveditor.core.tests.index.cache;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.cache.file.SVDBFileSystem;
import org.sveditor.core.db.index.cache.file.SVDBFileSystemDataInput;
import org.sveditor.core.db.index.cache.file.SVDBFileSystemDataOutput;

import org.sveditor.core.tests.SVCoreTestCaseBase;

public class TestIndexCacheFS extends SVCoreTestCaseBase {
	
	
	
	@Override
	protected void tearDown() throws Exception {
		// TODO Auto-generated method stub
//		super.tearDown();
	}

	public void testFSBasics() throws IOException {
		SVDBFileSystem fs = new SVDBFileSystem(fTmpDir, SVCorePlugin.getVersion());
		
		fs.init();
		
		List<byte[]> ref_data = new ArrayList<byte[]>();
		List<Integer> file_ids = new ArrayList<Integer>();
		
		for (int i=0; i<4; i++) {
			byte tdata[] = new byte[1024*1024*48];
//			byte tdata[] = new byte[1024*1024];
		
			for (int j=0; j<tdata.length; j++) {
				tdata[j] = (byte)(i+j);
			}
			
			ref_data.add(tdata);
		}
		
		for (int i=0; i<ref_data.size(); i++) {
			SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
		
			byte tdata[] = ref_data.get(i);
			
			for (int j=0; j<tdata.length; j++) {
				out.writeByte(tdata[j]);
			}
			
			int fileid = fs.writeFile("", out);
			file_ids.add(fileid);
		}
		
		for (int i=0; i<ref_data.size(); i++) {
			int check_id = (i+7) % ref_data.size();
//			int check_id = i;
			byte tdata[] = ref_data.get(check_id);
			int fileid = file_ids.get(check_id);
			
			System.out.println("Check " + fileid);
		
			SVDBFileSystemDataInput in = fs.readFile("", fileid);
			
			for (int j=0; j<tdata.length; j++) {
				int b = in.readByte();
				if (b != tdata[j]) {
					System.out.println("Byte " + j + " of file " + fileid + 
							" is incorrect: expect " + tdata[j] + " receive " + b);
				}
			}
		}
	
//		for (int i=0; i<2048; i++) {
		/*
		for (int i=0; i<8; i++) {
			SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
		
			long start, end;
			
			start = System.currentTimeMillis();
			for (int j=0; j<(1024*1024*8); j++) {
				out.writeByte(j);
			}
			end = System.currentTimeMillis();
			System.out.println("Write data: " + (end-start));
			
			start = System.currentTimeMillis();
			fs.writeFile(out);
			end = System.currentTimeMillis();
			System.out.println("Write file: " + (end-start));
			
		}
		 */
		
		fs.close();
	}

	public void testFSReopen() throws IOException {
		SVDBFileSystem fs = new SVDBFileSystem(fTmpDir, SVCorePlugin.getVersion());
		
		fs.init();
		
		List<byte[]> ref_data = new ArrayList<byte[]>();
		List<Integer> file_ids = new ArrayList<Integer>();
		
		for (int i=0; i<4; i++) {
			byte tdata[] = new byte[1024*1024*16];
		
			for (int j=0; j<tdata.length; j++) {
				tdata[j] = (byte)(i+j);
			}
			
			ref_data.add(tdata);
		}
		
		for (int i=0; i<ref_data.size(); i++) {
			SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
		
			byte tdata[] = ref_data.get(i);
			
			for (int j=0; j<tdata.length; j++) {
				out.writeByte(tdata[j]);
			}
			
			int fileid = fs.writeFile("", out);
			file_ids.add(fileid);
		}
		
		for (int i=0; i<ref_data.size(); i++) {
			int check_id = (i+7) % ref_data.size();
			byte tdata[] = ref_data.get(check_id);
			int fileid = file_ids.get(check_id);
			
			System.out.println("Check " + fileid);
		
			SVDBFileSystemDataInput in = fs.readFile("", fileid);
			
			for (int j=0; j<tdata.length; j++) {
				int b = in.readByte();
				if (b != tdata[j]) {
					System.out.println("Byte " + j + " of file " + fileid + 
							" is incorrect: expect " + tdata[j] + " receive " + b);
				}
			}
		}
	
		fs.close();
		
		fs = new SVDBFileSystem(fTmpDir, SVCorePlugin.getVersion());
		fs.init();
	
		for (int i=0; i<ref_data.size(); i++) {
			int check_id = (i+7) % ref_data.size();
			byte tdata[] = ref_data.get(check_id);
			int fileid = file_ids.get(check_id);
			
			System.out.println("Check " + fileid);
		
			SVDBFileSystemDataInput in = fs.readFile("", fileid);
			
			for (int j=0; j<tdata.length; j++) {
				int b = in.readByte();
				if (b != tdata[j]) {
					System.out.println("Byte " + j + " of file " + fileid + 
							" is incorrect: expect " + tdata[j] + " receive " + b);
				}
			}
		}
		
	}
	
	public void testFSDelete() throws IOException {
		SVDBFileSystem fs = new SVDBFileSystem(fTmpDir, SVCorePlugin.getVersion());
		
		fs.init();
		
		List<byte[]> ref_data = new ArrayList<byte[]>();
		List<Integer> file_ids = new ArrayList<Integer>();
		
		for (int i=0; i<4; i++) {
			byte tdata[] = new byte[1024*16];
		
			for (int j=0; j<tdata.length; j++) {
				tdata[j] = (byte)(i+j);
			}
			
			ref_data.add(tdata);
		}

		for (int x=0; x<4; x++) {
			for (int i=0; i<ref_data.size(); i++) {
				SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();

				byte tdata[] = ref_data.get(i);

				for (int j=0; j<tdata.length; j++) {
					out.writeByte(tdata[j]);
				}

				int fileid = fs.writeFile("", out);
				file_ids.add(fileid);
			}

			for (int i=0; i<ref_data.size(); i++) {
				int check_id = (i+7) % ref_data.size();
				//			int check_id = i;
				byte tdata[] = ref_data.get(check_id);
				int fileid = file_ids.get(check_id);

				System.out.println("Check " + fileid);

				SVDBFileSystemDataInput in = fs.readFile("", fileid);

				for (int j=0; j<tdata.length; j++) {
					int b = in.readByte();
					if (b != tdata[j]) {
						System.out.println("Byte " + j + " of file " + fileid + 
								" is incorrect: expect " + tdata[j] + " receive " + b);
					}
				}
			}

			for (int i=0; i<ref_data.size(); i++) {
				fs.deleteFile("", file_ids.get(i));
			}
			file_ids.clear();
		}
	
		fs.close();
	}

}

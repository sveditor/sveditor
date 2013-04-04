package net.sf.sveditor.core.tests.index.cache;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystemDataOutput;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestIndexCacheFS extends SVCoreTestCaseBase {
	
	
	
	@Override
	protected void tearDown() throws Exception {
		// TODO Auto-generated method stub
//		super.tearDown();
	}

	public void testFSBasics() throws IOException {
		SVDBFileSystem fs = new SVDBFileSystem(fTmpDir);
		
		fs.init();
		
		byte tmp[] = new byte[4096];
		for (int i=0; i<tmp.length; i++) {
			tmp[i] = (byte)i;
		}
		
		List<Integer> held_blocks = new ArrayList<Integer>();
	
//		for (int i=0; i<2048; i++) {
		for (int i=0; i<8; i++) {
			SVDBFileSystemDataOutput out = new SVDBFileSystemDataOutput();
			
			for (int j=0; j<16384; j++) {
				out.writeByte(j);
			}
			
			fs.writeFile(out);
			
			/*
			int id = fs.allocBlock();
			fs.writeBlock(id, tmp);
			System.out.println("Write block " + id);
			held_blocks.add(id);
			
			if (held_blocks.size() > 8) {
				int idx = (int)(System.nanoTime() % held_blocks.size());
				id = held_blocks.remove(idx);
				System.out.println("Free block " + id);
				fs.freeBlock(id);
			}
			 */
		}
		
		fs.close();
	}

}

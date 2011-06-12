package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInput;
import java.io.DataInputStream;
import java.io.DataOutput;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.CoreException;
import org.osgi.framework.Bundle;

public class TestPersistencePerformance extends TestCase {
	
	public void testInMemPersistence() throws IOException, CoreException, DBFormatException, DBWriteException {
		SVDBPersistenceWriter writer = new SVDBPersistenceWriter();
		SVDBPersistenceReader reader = new SVDBPersistenceReader();
		
		ByteArrayOutputStream bos = null;
		Bundle bundle = SVCorePlugin.getDefault().getBundle(); 
		URL cls_url = bundle.getEntry("/sv_builtin/string.svh");
		InputStream cls_in = cls_url.openStream();
		String content = TestUtils.readInput(cls_in);
		SVDBFile file = SVDBTestUtils.parse(content, "string.svh");
		
		try {
			cls_in.close();
		} catch (IOException e) {}

		bos = new ByteArrayOutputStream();
		DataOutput out = new DataOutputStream(bos);
		writer.init(out);
		writer.writeSVDBItem(file);

		long start = System.currentTimeMillis();
		for (int i=0; i<10000; i++) {
			ByteArrayInputStream ba_in = new ByteArrayInputStream(bos.toByteArray());
			DataInput in = new DataInputStream(ba_in);
			
			reader.init(in);
			reader.readSVDBItem(null);
		}
		long end = System.currentTimeMillis();
		
		System.out.println("1000 loads in " + (end-start) + "ms");
	}

}

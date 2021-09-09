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
package org.sveditor.core.tests.index.external;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

import org.sveditor.core.db.index.external.ExternalIndexerMsg;

import junit.framework.TestCase;
import org.sveditor.core.tests.SVCoreTestCaseBase;

public class TestExternalIndexerMessaging extends SVCoreTestCaseBase {
	
	public void testDataPackUnpack() {
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
	
		// Write 32-bit values
		int i_vals[] = new int[] {
				0, 1, 2, 3, 
				0x7fffeeaa, 
				-1, -2, -3, -4};
		for (int val : i_vals) {
			msg.write32(val);
		}
		
		msg.init_read();
		
		for (int val : i_vals) {
			int r_val = msg.read32();
			assertEquals(val, r_val);
		}
		
		// Write 64-bit values
		msg.init_write();
		long l_vals[] = new long[] {
				0, 3, 4, 5, 
				0x7fffeeaa8088FFEEL, 
				-1, -2, -3, -4};
		for (long val : l_vals) {
			msg.write64(val);
		}
		
		msg.init_read();
		
		for (long val : l_vals) {
			long r_val = msg.read64();
			assertEquals(val, r_val);
		}		
		
		msg.init_write();
		
		String s_vals[] = new String[] {
				"Hello",
				"World"
		};
		
		for (String val : s_vals) {
			msg.write_str(val);
		}
		
		msg.init_read();
		
		for (String val : s_vals) {
			String r_val = msg.read_str();
			assertEquals(val, r_val);
		}
	}
	
	public void testSendRecv() throws IOException {
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		
		String exp_data = "Hello World";
		
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
		msg.write_str(exp_data);
		
		msg.send(bos);
		
	
		ByteArrayInputStream bin = new ByteArrayInputStream(
				bos.toByteArray());
		
		ExternalIndexerMsg r_msg = new ExternalIndexerMsg();
		r_msg.recv(bin);
		
		String data = r_msg.read_str();
		
		assertEquals(exp_data, data);
	}
	
	public void testSendRecv4KMessage() throws IOException {
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
		for (int i=0; i<1024; i++) {
			msg.write32(i);
		}
		
		msg.send(bos);
	
		ByteArrayInputStream bin = new ByteArrayInputStream(
				bos.toByteArray());
		
		ExternalIndexerMsg r_msg = new ExternalIndexerMsg();
		r_msg.recv(bin);
		
		for (int i=0; i<1024; i++) {
			int val = r_msg.read32();
			
			assertEquals(i, val);
		}
	}	
}

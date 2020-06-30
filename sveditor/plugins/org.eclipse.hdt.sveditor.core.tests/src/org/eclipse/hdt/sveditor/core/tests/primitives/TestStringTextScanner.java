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
package org.eclipse.hdt.sveditor.core.tests.primitives;

import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;

import junit.framework.TestCase;

public class TestStringTextScanner extends TestCase {
	
	public void testIdxPostDelete() {
		StringTextScanner scanner;
		
		scanner = new StringTextScanner("0123456789ABCDEF");
		
		for (int i=0; i<5; i++) {
			assertEquals(i, scanner.getOffset());
			assertEquals((char)('0'+i), scanner.charAt(scanner.getOffset()));
			int ch = scanner.get_ch();
			assertEquals((char)('0'+i), (char)ch);
		}
		
		assertEquals(5, scanner.getOffset());
	
		// Delete all before the current index
		// Ensure that the offset shrinks accordingly
		scanner.delete(3, 5);
		
		assertEquals("01256789ABCDEF", scanner.getStorage().toString());
		assertEquals(3, scanner.getOffset());
		assertEquals(14, scanner.getLimit());
		
		scanner = new StringTextScanner("0123456789ABCDEF");
		
		for (int i=0; i<5; i++) {
			assertEquals(i, scanner.getOffset());
			assertEquals((char)('0'+i), scanner.charAt(scanner.getOffset()));
			int ch = scanner.get_ch();
			assertEquals((char)('0'+i), (char)ch);
		}
		
		assertEquals(5, scanner.getOffset());
	
		// Delete a region bridging the current index
		// Ensure that the offset shrinks accordingly
		scanner.delete(3, 8);
		
		assertEquals("01289ABCDEF", scanner.getStorage().toString());
		assertEquals(3, scanner.getOffset());
		assertEquals('8', (char)scanner.get_ch());
		assertEquals(11, scanner.getLimit());
	}

	public void testUngetIdxPostDelete() {
		StringTextScanner scanner;
		int ch;
		
		scanner = new StringTextScanner("0123456789ABCDEF");
		
		for (int i=0; i<5; i++) {
			assertEquals(i, scanner.getOffset());
			assertEquals((char)('0'+i), scanner.charAt(scanner.getOffset()));
			ch = scanner.get_ch();
			assertEquals((char)('0'+i), (char)ch);
		}
		
		ch = scanner.get_ch();
		scanner.unget_ch(ch);
		
		assertEquals(5, scanner.getOffset());
	
		// Delete all before the current index
		// Ensure that the offset shrinks accordingly
		scanner.delete(3, 5);
		
		assertEquals("01256789ABCDEF", scanner.getStorage().toString());
		assertEquals(3, scanner.getOffset());
		assertEquals(14, scanner.getLimit());
		
		scanner = new StringTextScanner("0123456789ABCDEF");
		
		for (int i=0; i<5; i++) {
			assertEquals(i, scanner.getOffset());
			assertEquals((char)('0'+i), scanner.charAt(scanner.getOffset()));
			ch = scanner.get_ch();
			assertEquals((char)('0'+i), (char)ch);
		}
		
		ch = scanner.get_ch();
		scanner.unget_ch(ch);
		
		assertEquals(5, scanner.getOffset());
	
		// Delete a region bridging the current index
		// Ensure that the offset shrinks accordingly
		scanner.delete(3, 8);
		
		assertEquals("01289ABCDEF", scanner.getStorage().toString());
		assertEquals(3, scanner.getOffset());
		assertEquals('8', (char)scanner.get_ch());
		assertEquals(11, scanner.getLimit());
	}

}

/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParseException;

public class TestParseDataTypes extends TestCase {
	
	public void testTypedefVirtual() throws SVParseException {
		String content =
			"class foobar;\n" +
			"    typedef virtual my_if #(FOO, BAR, BAZ) my_if_t;\n" +
			"\n" +
			"endclass\n";
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBModIfcClassDecl cls =
			parser.parsers().classParser().parse(0);
		
		for (SVDBItem it : cls.getItems()) {
			System.out.println("it " + it.getType() + " " + it.getName());
		}
	}

}

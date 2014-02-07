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


package net.sf.sveditor.core.tests.lexer;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ISVParser;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.parser.SVParsers;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class TestClassItems extends TestCase {
	
	public void testClassFields() {
		String content = 
			"class __sv_builtin_covergroup_options;\n" +
			"	int 	weight;\n" + 
			"\n" +
			"	real 	goal;\n" +
			"\n" +
			"	string 	name;\n" +
			"\n" +
			"	string 	comment;\n" +
			"\n" +
			"	int		at_least;\n" +
			"\n" +
			"	bit		detect_overlap;\n" +
			"\n" +
			"	int		auto_bin_max;\n" +
			"\n" +
			"	bit		per_instance;\n" +
			"\n" +
			"	bit		cross_num_print_missing;\n" +
			"\n" +
			"endclass\n";

		final LogHandle log = LogFactory.getLogHandle("testClassFields");
		final SVLexer lexer = new SVLexer();
		ISVParser parser = new ISVParser() {
			
			public void warning(String msg, int lineno) {}
			
			public SVParsers parsers() {
				return null;
			}
			
			public SVLexer lexer() {
				return lexer;
			}
			
			public ILogHandle getLogHandle() { return log; }
			
			public boolean error_limit_reached() {return false;}
			
			public void disableErrors(boolean dis) {}
			
			public void error(SVParseException e) {}
			
			public void error(String msg) {}
			
			public void debug(String msg, Exception e) {}

			public SVParserConfig getConfig() {
				return null;
			}
			public String getFilename(SVDBLocation loc) {
				return "Unknown: " + loc.getFileId();
			}
		};
		lexer.init(parser, new StringTextScanner(content));
		
		while (lexer.peek() != null) {
			log.debug("token: \"" + lexer.getImage() + "\"");
			lexer.eatToken();
		}
		LogFactory.removeLogHandle(log);
	}

}

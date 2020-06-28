/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package net.sf.sveditor.core.tests.lexer;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.ISVParser;
import org.eclipse.hdt.sveditor.core.parser.SVLexer;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;
import org.eclipse.hdt.sveditor.core.parser.SVParsers;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;

import junit.framework.TestCase;

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
			public String getFilename(long loc) {
				return "Unknown: " + SVDBLocation.unpackFileId(loc);
			}

			@Override
			public void enter_type_scope(ISVDBItemBase item) {
				// TODO Auto-generated method stub
				
			}

			@Override
			public void leave_type_scope(ISVDBItemBase item) {
				// TODO Auto-generated method stub
				
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

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
package org.eclipse.hdt.sveditor.core.argfile.filter;

import java.io.ByteArrayOutputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileLexer;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileParser;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;

public class StringArgFileFilter {
	private String				fBaseLocation;
	
	public StringArgFileFilter() {
		fBaseLocation = "";
	}

	public String filter(String content, ArgFileFilterList filter) {
		SVArgFileParser parser = new SVArgFileParser(
				fBaseLocation, fBaseLocation, new SVDBWSFileSystemProvider());

		SVDBFile file = new SVDBFile("");
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
	
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, new StringTextScanner(content));
		
		parser.init(lexer, "");
	
		try {
			parser.parse(file, markers);
		} catch (SVParseException e) {}
	
		if (filter != null) {
			file = filter.filter(file);
		}
		
		ArgFileWriter writer = new ArgFileWriter();
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		
		writer.write(file, out);
		
		return out.toString();
	}
}

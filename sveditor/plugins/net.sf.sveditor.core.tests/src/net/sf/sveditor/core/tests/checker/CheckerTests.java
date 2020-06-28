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
package net.sf.sveditor.core.tests.checker;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.checker.ISVDBCheckErrorReporter;
import org.eclipse.hdt.sveditor.core.checker.ISVDBChecker;
import org.eclipse.hdt.sveditor.core.checker.SVDBFileCheckerFactory;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.SVDBUtil;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBMarkerMgr;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.hdt.sveditor.core.preproc.ISVPreProcFileMapper;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class CheckerTests extends TestSuite {
	
	public CheckerTests() {
		
	}
	
	public static TestSuite suite() {
		return new CheckerTests();
	}

	public static void runTest(
			final String		name,
			String				content,
			String	...			errors) throws SVParseException {
		LogHandle log = LogFactory.getLogHandle(name);
		final List<SVDBMarker> check_markers = new ArrayList<SVDBMarker>();
		List<SVDBMarker> expected_errors = new ArrayList<SVDBMarker>();
		
		for (String err : errors) {
			// <lineno>:<message>
			int colon_idx = err.indexOf(':');
			TestCase.assertTrue(colon_idx != -1);
			
			int lineno = -1;
			try {
				lineno = Integer.parseInt(err.substring(0, colon_idx));
			} catch (NumberFormatException e) {
				TestCase.fail(e.getMessage());
			}
			
			String msg = err.substring(colon_idx+1);
		
			expected_errors.add(new SVDBMarker(
					SVDBMarker.MarkerType.Error,
					SVDBMarker.MarkerKind.SemanticError,
					msg,
					SVDBLocation.pack(1, lineno, 1)));
		}
		
		TestCase.assertEquals(errors.length, expected_errors.size());
		
		ISVPreProcFileMapper mapper = new ISVPreProcFileMapper() {
			
			@Override
			public int mapFilePathToId(String path, boolean add) {
				return 1;
			}
			
			@Override
			public String mapFileIdToPath(int id) {
				return name;
			}
		};
		
		ISVDBMarkerMgr marker_mgr = new ISVDBMarkerMgr() {
			
			@Override
			public void clearMarkers(String path) { }
			
			@Override
			public void addMarker(String path, String type, int lineno, String msg) {
				check_markers.add(new SVDBMarker(
						SVDBMarker.MarkerType.Error,
						SVDBMarker.MarkerKind.SemanticError, 
						msg, 
						SVDBLocation.pack(1, lineno, 1)));
			}
		};

		try {
			List<SVDBMarker> parse_markers = new ArrayList<SVDBMarker>();
			ISVDBChecker checker = SVDBFileCheckerFactory.create(marker_mgr, mapper);
			SVDBFile file = SVDBTestUtils.parse(log, content, name, parse_markers);
	
			for (SVDBMarker m : parse_markers) {
				log.debug("Error: " + m.getMessage() + " line=" + 
						SVDBLocation.unpackLineno(m.getLocation()));
			}
			TestCase.assertEquals(0, parse_markers.size());
			
			checker.check(file);
			
			TestCase.assertEquals(expected_errors.size(), check_markers.size());
		} finally {
			LogFactory.removeLogHandle(log);
		}
	}
			
}

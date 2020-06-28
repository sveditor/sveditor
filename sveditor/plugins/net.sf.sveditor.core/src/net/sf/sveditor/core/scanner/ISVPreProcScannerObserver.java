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


package net.sf.sveditor.core.scanner;

import java.util.List;

import net.sf.sveditor.core.Tuple;

public interface ISVPreProcScannerObserver {
	
	void init(ISVScanner scanner);
	
	void enter_file(String filename);
	
	void leave_file();

	void preproc_define(
			String 							key, 
			List<Tuple<String,String>> 		params, 
			String 							value);
	
	void preproc_include(String path);
	
	void enter_preproc_conditional(String type, String conditional);
	
	void leave_preproc_conditional();
	
	void comment(String title, String comment);

	void enter_package(String name);
	
	void leave_package();

}

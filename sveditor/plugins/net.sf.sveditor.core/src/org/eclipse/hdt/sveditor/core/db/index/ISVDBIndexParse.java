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
package org.eclipse.hdt.sveditor.core.db.index;

import java.io.InputStream;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.preproc.ISVStringPreProcessor;

/**
 * Implements the 'parseable' interface for ISVDBIndex
 * 
 * @author ballance
 *
 */
public interface ISVDBIndexParse {

	Tuple<SVDBFile, SVDBFile> parse(
			IProgressMonitor monitor,
			InputStream in, 
			String path, 
			List<SVDBMarker> markers);

	/**
	 * Creates a pre-processor for the specified path
	 * 
	 * @param path
	 * @return
	 */
	ISVStringPreProcessor createPreProc(
			String 				path,
			InputStream			in,
			int					limit_lineno);
}

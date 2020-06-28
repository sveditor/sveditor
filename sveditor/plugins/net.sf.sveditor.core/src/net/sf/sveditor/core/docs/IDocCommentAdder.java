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
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs;

import java.util.ArrayList;

import net.sf.sveditor.core.Tuple;

public interface IDocCommentAdder {
	
	/**
	 * Adds a comment to above the member at startline
	 * 
	 * @param startline - line to add comment above
	 * 
	 * @return
	 * An array list comprised of "Line number" and comments to be added
	 */
	ArrayList<Tuple<Object, String>> AddComments (int startline);
	
	/**
	 * Sets the line delimiter to be used.... defaults to \n
	 * @param linedelimiter
	 */
	void SetLineDelimiter(String linedelimiter);
}

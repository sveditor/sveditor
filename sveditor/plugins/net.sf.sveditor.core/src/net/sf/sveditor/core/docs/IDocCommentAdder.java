/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
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
	ArrayList<Tuple<Object, String>> addcomments (int startline);
	
	/**
	 * Sets the line delimiter to be used.... defaults to \n
	 * @param linedelimiter
	 */
	void SetLineDelimiter(String linedelimiter);
}

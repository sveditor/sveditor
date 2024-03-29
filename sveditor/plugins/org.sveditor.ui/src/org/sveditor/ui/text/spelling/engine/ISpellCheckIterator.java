/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/

package org.sveditor.ui.text.spelling.engine;

import java.util.Iterator;

/**
 * Interface for iterators used for spell checking.
 *
 * @since 3.0
 */
public interface ISpellCheckIterator extends Iterator<String> {

	/**
	 * Returns the begin index (inclusive) of the current word.
	 *
	 * @return The begin index of the current word
	 */
	public int getBegin();

	/**
	 * Returns the end index (exclusive) of the current word.
	 *
	 * @return The end index of the current word
	 */
	public int getEnd();

	/**
	 * Does the current word start a new sentence?
	 *
	 * @return <code>true<code> iff the current word starts a new sentence, <code>false</code> otherwise
	 */
	public boolean startsSentence();

	/**
	 * Tells whether to ignore single letters
	 * from being checked.
	 *
	 * @since 3.3
	 * @param state <code>true</code> if single letters should be ignored
	 */
	public void setIgnoreSingleLetters(boolean state);
}

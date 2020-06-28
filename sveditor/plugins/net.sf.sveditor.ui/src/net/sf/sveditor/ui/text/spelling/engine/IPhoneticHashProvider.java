/*******************************************************************************
 * Copyright (c) 2000, 2005 IBM Corporation and others.
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

package net.sf.sveditor.ui.text.spelling.engine;

/**
 * Interface of hashers to compute the phonetic hash for a word.
 *
 * @since 3.0
 */
public interface IPhoneticHashProvider {

	/**
	 * Returns the phonetic hash for the word.
	 *
	 * @param word
	 *                  The word to get the phonetic hash for
	 * @return The phonetic hash for the word
	 */
	public String getHash(String word);

	/**
	 * Returns an array of characters to compute possible mutations.
	 *
	 * @return Array of possible mutator characters
	 */
	public char[] getMutators();
}

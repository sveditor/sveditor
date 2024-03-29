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

package org.sveditor.ui.text.spelling.engine;

/**
 * Interface of algorithms to compute the phonetic distance between two words.
 *
 * @since 3.0
 */
public interface IPhoneticDistanceAlgorithm {

	/**
	 * Returns the non-negative phonetic distance between two words
	 *
	 * @param from
	 *                  The first word
	 * @param to
	 *                  The second word
	 * @return The non-negative phonetic distance between the words.
	 */
	public int getDistance(String from, String to);
}

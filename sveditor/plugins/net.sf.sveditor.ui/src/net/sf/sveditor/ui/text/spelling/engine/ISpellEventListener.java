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
 * Interface for spell event listeners.
 *
 * @since 3.0
 */
public interface ISpellEventListener {

	/**
	 * Handles a spell event.
	 *
	 * @param event
	 *                  Event to handle
	 */
	public void handle(ISpellEvent event);
}

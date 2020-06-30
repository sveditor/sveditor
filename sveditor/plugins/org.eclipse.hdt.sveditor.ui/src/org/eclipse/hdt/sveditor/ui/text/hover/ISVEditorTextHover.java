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
 *     Armond Paiva - repurposed from JDT for use in SVEditor
 *******************************************************************************/
package org.eclipse.hdt.sveditor.ui.text.hover;

import org.eclipse.jface.text.ITextHover;

import org.eclipse.ui.IEditorPart;


/**
 * Provides a hover popup which appears on top of an editor with relevant
 * display information. If the text hover does not provide information no
 * hover popup is shown.
 * <p>
 * Clients may implement this interface.
 * </p>
 *
 * @see org.eclipse.ui.IEditorPart
 * @see org.eclipse.jface.text.ITextHover
 *
 */
public interface ISVEditorTextHover extends ITextHover {

	/**
	 * Sets the editor on which the hover is shown.
	 *
	 * @param editor the editor on which the hover popup should be shown
	 */
	void setEditor(IEditorPart editor);

}


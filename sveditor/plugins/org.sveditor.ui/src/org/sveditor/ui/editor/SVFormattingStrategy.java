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


package org.sveditor.ui.editor;

import org.eclipse.jface.text.formatter.ContextBasedFormattingStrategy;

public class SVFormattingStrategy extends ContextBasedFormattingStrategy {

	@Override
	public void format() {
		super.format();
		System.out.println("format()");
	}

	@Override
	public String format(String content, boolean start, String indentation,
			int[] positions) {
		System.out.println("format: \"" + content + "\"; start=" + start + " indentation=\"" + indentation + "\"");
		return super.format(content, start, indentation, positions);
	}

	
}

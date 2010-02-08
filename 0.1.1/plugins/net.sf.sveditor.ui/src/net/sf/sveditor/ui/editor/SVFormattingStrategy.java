/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.formatter.ContextBasedFormattingStrategy;
import org.eclipse.jface.text.formatter.IFormattingStrategy;

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

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
package org.sveditor.core;

import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.content.IContentDescriber;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.ITextContentDescriber;

public class SVContentDescriber 
	implements IContentDescriber, ITextContentDescriber {

	public SVContentDescriber() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public int describe(InputStream contents, IContentDescription description) throws IOException {
		return INDETERMINATE;
	}

	@Override
	public QualifiedName[] getSupportedOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int describe(Reader contents, IContentDescription description) throws IOException {
		// TODO Auto-generated method stub
		return 0;
	}
	

}

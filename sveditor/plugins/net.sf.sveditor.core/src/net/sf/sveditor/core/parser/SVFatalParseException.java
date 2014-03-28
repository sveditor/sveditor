/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;

public class SVFatalParseException extends RuntimeException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 4266897253069702084L;
	
	public SVFatalParseException(String msg) {
		super(msg);
	}

}

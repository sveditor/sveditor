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


package org.eclipse.hdt.sveditor.core.db.expr;

public class SVExprParseException extends Exception {
	
	private static final long serialVersionUID = 4403018861977065475L;

	public SVExprParseException(String msg) {
		super(msg);
	}
	
	public SVExprParseException(Exception e) {
		super(e);
	}

}

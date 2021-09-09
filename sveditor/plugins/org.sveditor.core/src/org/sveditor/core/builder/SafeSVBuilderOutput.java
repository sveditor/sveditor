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
package org.sveditor.core.builder;

public class SafeSVBuilderOutput implements ISVBuilderOutput {
	private ISVBuilderOutput		fOut;
	
	public SafeSVBuilderOutput(ISVBuilderOutput out) {
		fOut = out;
	}

	@Override
	public void println(String msg) {
		if (fOut != null) {
			fOut.println(msg);
		}
	}

	@Override
	public void note(String msg) {
		if (fOut != null) {
			fOut.note(msg);
		}
	}

	@Override
	public void errln(String msg) {
		if (fOut != null) {
			fOut.errln(msg);
		} 
	}
	
	public void error(String msg) {
		if (fOut != null) {
			fOut.error(msg);
		}
	}

}

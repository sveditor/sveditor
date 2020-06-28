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
package net.sf.sveditor.core.builder;

public class CoreBuilderOutputListener implements ISVBuilderOutputListener {

	@Override
	public void println(String project, String msg) {
		System.out.println("[" + project + "] " + msg);
	}

	@Override
	public void errln(String project, String msg) {
		System.err.println("[" + project + "] " + msg);
	}

}

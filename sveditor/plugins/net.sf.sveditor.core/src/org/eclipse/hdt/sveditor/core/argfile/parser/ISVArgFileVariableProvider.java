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
package org.eclipse.hdt.sveditor.core.argfile.parser;

import java.util.List;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.Tuple;

public interface ISVArgFileVariableProvider {

	/**
	 * Returns true|false depending on whether the provider
	 * provides this variable
	 * 
	 * @param var
	 * @return
	 */
	boolean providesVar(String var);

	/**
	 * Expands variable 'var' and returns the expansion
	 * 
	 * @param var
	 * @return
	 */
	String expandVar(String var);

	/**
	 * Returns the list of variables requested by clients
	 * 
	 * @return
	 */
	List<Tuple<String, String>> getRequestedVars();

	/**
	 * Returns variables provided by this provider
	 * @return
	 */
	Set<String> getVariables();
}

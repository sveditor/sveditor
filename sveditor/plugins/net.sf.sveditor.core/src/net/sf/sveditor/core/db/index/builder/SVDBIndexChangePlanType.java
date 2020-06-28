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
package net.sf.sveditor.core.db.index.builder;

public enum SVDBIndexChangePlanType {
	/**
	 * An empty plan indicates no need to do any work
	 */
	Empty,

	/**
	 * Requests a refresh operation on the index. This 
	 * may result in a new plan being computed
	 */
	Refresh,
	
	/**
	 * Requests rebuild of specific files. 
	 */
	RebuildFiles,
	
	/**
	 * Remove the specified files from the index
	 */
	RemoveFiles,
	
	/**
	 * Requests rebuild of the full index
	 */
	RebuildIndex,
	
	/**
	 * Composite plan involving multiple indexes
	 */
	Composite

}

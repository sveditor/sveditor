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


package org.sveditor.core.log;

public interface ILogHandle extends ILogLevel {
	String				LOG_CAT_DEFAULT = "DEFAULT";
	String				LOG_CAT_PARSER  = "Parser";
	
	
	String getName();
	
	void init(ILogListener parent);
	
	void print(int type, int level, String msg);
	
	void println(int type, int level, String msg);
	
	boolean isEnabled();
	
	int getDebugLevel();
	
	void setDebugLevel(int level);
	
	void addLogLevelListener(ILogLevelListener l);
	
}

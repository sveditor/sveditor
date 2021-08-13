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
package org.eclipse.hdt.sveditor.core.db.index;

public interface ISVDBMarkerMgr {
	String				MARKER_TYPE_ERROR   = "ERROR";
	String				MARKER_TYPE_WARNING = "WARNING";
	String				MARKER_TYPE_INFO    = "INFO";
	String				MARKER_TYPE_TASK    = "TASK";

	void addMarker(
			String 			path,
			String			type,
			int				lineno,
			String			msg);
			
	void clearMarkers(String path);
	
}

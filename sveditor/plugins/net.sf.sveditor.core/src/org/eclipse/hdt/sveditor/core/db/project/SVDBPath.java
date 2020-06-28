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


package org.eclipse.hdt.sveditor.core.db.project;


public class SVDBPath {
	
	private String					fPath;
	private boolean					fPhantom;

	public SVDBPath(String path) {
		fPath        = path;
		fPhantom     = false;
	}

	public SVDBPath(String path, boolean is_phantom) {
		fPath        = path;
		fPhantom     = is_phantom;
	}

	/**
	 * Indicates whether this path entry belongs in the .svproject file
	 * @return
	 */
	public boolean getIsPhantom() {
		return fPhantom;
	}
	
	public void setIsPhantom(boolean is_phantom) {
		fPhantom = is_phantom;
	}
	
	public String getPath() {
		return fPath;
	}
	
	public void setPath(String path) {
		fPath = path;
	}
	
	public SVDBPath duplicate() {
		return new SVDBPath(fPath, fPhantom);
	}
	
	public boolean equals(Object other) {
		if (other instanceof SVDBPath) {
			SVDBPath other_p = (SVDBPath)other;
			
			if (other_p.fPath.equals(fPath)) {
				return true;
			}
		}
		return false;
	}
}

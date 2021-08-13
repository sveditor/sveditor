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
package org.sveditor.core.script.launch;

public class ScriptMessage {
	public enum MessageType {
		Note,
		Warning,
		Error
	}

	private String				fMarkerType;
	private String				fMessage;
	private String				fDescription;
	private String				fPath;
	private int					fLineno;
	private MessageType			fType;
	
	public ScriptMessage(
			String			path,
			int				lineno,
			String			message,
			MessageType		type) {
		fPath = path;
		fLineno = lineno;
		fMessage = message;
		fType = type;
		fMarkerType = null;
	}
	
	public boolean isValid() {
		return (fPath != null && fMessage != null &&
				fLineno != -1);
	}
	
	public void setMarkerType(String type) {
		fMarkerType = type;
	}
	
	public String getMarkerType() {
		return fMarkerType;
	}
	
	public String getMessage() {
		return fMessage;
	}
	
	public void setMessage(String msg) {
		fMessage = msg;
	}
	
	public void setDescription(String d) {
		fDescription = d;
	}
	
	public String getDescription() {
		return fDescription;
	}

	public String getPath() {
		return fPath;
	}
	
	public void setPath(String path) {
		fPath = path;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public void setLineno(int lineno) {
		fLineno = lineno;
	}
	
	public MessageType getType() {
		return fType;
	}
	
}

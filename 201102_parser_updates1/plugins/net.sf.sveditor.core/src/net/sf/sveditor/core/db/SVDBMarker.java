/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;


public class SVDBMarker extends SVDBItemBase {
	public enum MarkerType {
		Info,
		Warning,
		Error
	};
	
	public enum MarkerKind {
		MissingInclude,
		UndefinedMacro,
		ParseError
	};
	
	private String					fMessage;
	private MarkerKind				fKind;
	private MarkerType				fMarkerType;

	public SVDBMarker() {
		super(SVDBItemType.Marker);
	}
	
	public SVDBMarker(
			MarkerType	type,
			MarkerKind	kind,
			String 		message) {
		super(SVDBItemType.Marker);
		fMarkerType = type;
		fKind    	= kind;
		fMessage 	= message;
	}
	
	public MarkerType getMarkerType() {
		return fMarkerType;
	}
	
	public void setMarkerType(MarkerType type) {
		fMarkerType = type;
	}
	
	public void setMessage(String msg) {
		fMessage = msg;
	}
	
	public String getMessage() {
		return fMessage;
	}
	
	public void setKind(MarkerKind kind) {
		fKind = kind;
	}
	
	public MarkerKind getKind() {
		return fKind;
	}

	@Override
	public SVDBMarker duplicate() {
		return (SVDBMarker)SVDBItemUtils.duplicate(this);
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBMarker) {
			SVDBMarker o = (SVDBMarker)obj;
			boolean ret = super.equals(obj);
			
			ret &= (o.fKind == fKind);
			
			return ret;
		}
		
		return false;
	}
	
}

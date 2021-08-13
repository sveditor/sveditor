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


package org.eclipse.hdt.sveditor.core.db;



public class SVDBMarker extends SVDBItemBase {
	public enum MarkerType {
		Info,
		Warning,
		Error,
		Task
	};
	
	public enum MarkerKind {
		Info,
		MissingInclude,
		UndefinedMacro,
		UnbalancedDirective,
		ParseError,
		SemanticError
	};
	
	public String					fMessage;
	public MarkerKind				fKind;
	public MarkerType				fMarkerType;

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
	
	public SVDBMarker(
			MarkerType		type,
			MarkerKind		kind,
			String 			message,
			long			loc) {
		this(type, kind, message);
		setLocation(loc);
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

			ret &= (o.fMarkerType == fMarkerType);
			ret &= (o.fKind == fKind);
			ret &= o.fMessage.equals(fMessage);
			
			ret &= o.fLocation == fLocation;
			
			return ret;
		}
		
		return false;
	}
	
}

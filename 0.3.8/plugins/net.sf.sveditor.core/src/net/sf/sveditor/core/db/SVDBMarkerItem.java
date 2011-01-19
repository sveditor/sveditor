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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBMarkerItem extends SVDBItem {
	
	public static final String			MARKER_ERR  = "ERROR";
	public static final String			MARKER_WARN = "WARNING";
	
	public static final String			MARKER_KIND = "KIND";
	
	public static final String			KIND_MISSING_INC = "KIND_MISSING_INCLUDE";
	public static final String			MISSING_INC_PATH = "MISSING_INC_PATH";
	
	public static final String			KIND_UNDEFINED_MACRO = "KIND_UNDEFINED_MACRO";
	public static final String			UNDEFINED_MACRO      = "UNDEFINED_MACRO";
	
	public static final String			KIND_GENERIC     = "KIND_GENERIC";
	
	private String					fMessage;
	private String					fKind;
	private Map<String, String>		fAttr;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBMarkerItem(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.Marker); 
	}
	
	public SVDBMarkerItem(
			String 		name,
			String		kind,
			String 		message) {
		super(name, SVDBItemType.Marker);
		fKind    	= kind;
		fMessage 	= message;
		fAttr		= new HashMap<String, String>();
	}
	
	public SVDBMarkerItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fMessage = reader.readString();
		fKind    = reader.readString();

		fAttr		= new HashMap<String, String>();

		List<String> attr = reader.readStringList();
		for (int i=0; i<attr.size(); i+=2) {
			fAttr.put(attr.get(i), attr.get(i+1));
		}
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fMessage);
		writer.writeString(fKind);
		
		List<String> attr = new ArrayList<String>();
		for (Entry<String, String> e : fAttr.entrySet()) {
			attr.add(e.getKey());
			attr.add(e.getValue());
		}
		writer.writeStringList(attr);
	}

	public void setMessage(String msg) {
		fMessage = msg;
	}
	
	public String getMessage() {
		return fMessage;
	}
	
	public void setKind(String kind) {
		fKind = kind;
	}
	
	public String getKind() {
		return fKind;
	}

	public void setAttr(String key, String value) {
		if (fAttr.containsKey(key)) {
			fAttr.remove(key);
		}
		fAttr.put(key, value);
	}
	
	public String getAttr(String key) {
		return fAttr.get(key);
	}
	
	@Override
	public SVDBItemBase duplicate() {
		SVDBMarkerItem ret = new SVDBMarkerItem(getName(), getKind(), getMessage());
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		SVDBMarkerItem m = (SVDBMarkerItem)other;
		
		super.init(other);
		
		fMessage = m.fMessage; 
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBMarkerItem) {
			SVDBMarkerItem o = (SVDBMarkerItem)obj;
			
			if (!o.fMessage.equals(fMessage) ||
					o.fKind != fKind || o.fAttr != fAttr) {
				return false;
			}
			
			return super.equals(obj);
		}
		
		return false;
	}
	
}

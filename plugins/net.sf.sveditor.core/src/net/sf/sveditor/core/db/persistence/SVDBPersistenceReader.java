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


package net.sf.sveditor.core.db.persistence;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;

@SuppressWarnings("rawtypes")
public class SVDBPersistenceReader implements IDBReader {
	private InputStream			fIn;
	private byte				fBuf[];
	private int					fBufIdx;
	private int					fBufSize;
	private int					fUngetCh;
	private StringBuilder		fTmpBuffer;
	private static Map<Class, List<Enum>>		fEnumMap;
	private static final Map<SVDBItemType, ISVDBPersistenceFactory>	fSVDBFactoryMap;
	
	static {
		fSVDBFactoryMap = new HashMap<SVDBItemType, ISVDBPersistenceFactory>();
		
		fEnumMap = new HashMap<Class, List<Enum>>();
	}

	public SVDBPersistenceReader(InputStream in) {
		fIn      	= in;
		fBuf     	= new byte[1024*1024];
		fBufIdx  	= 0;
		fBufSize 	= 0;
		fUngetCh	= -1;
		fTmpBuffer 	= new StringBuilder();
	}
	
	public void init(InputStream in) {
		fIn = in;
		fUngetCh = -1;
		fBufIdx  = 0;
		fBufSize = 0;
	}
	
	public static void registerPersistenceFactory(
			ISVDBPersistenceFactory factory,
			SVDBItemType 	...		types) {
		for (SVDBItemType type : types) {
			if (fSVDBFactoryMap.containsKey(type)) {
				fSVDBFactoryMap.remove(type);
			}
			fSVDBFactoryMap.put(type, factory);
		}
	}

	public static void registerEnumType(Class enum_type, Enum values[]) {
		List<Enum> enum_list = new ArrayList<Enum>();
		for (Enum e : values) {
			enum_list.add(e);
		}
		
		fEnumMap.put(enum_type, enum_list);
	}
	
	public static int getEnumIndex(Class enum_type, Enum value) {
		List<Enum> enum_list = fEnumMap.get(enum_type);
		return enum_list.indexOf(value);
	}

	public String readBaseLocation() throws DBFormatException {
		String SDB = readTypeString();
		
		if (!"SDB".equals(SDB)) {
			throw new DBFormatException("Database not prefixed with SDB (" + SDB + ")");
		}
		
		int ch;
		
		if ((ch = getch()) != '<') {
			throw new DBFormatException("Missing '<'");
		}
		
		fTmpBuffer.setLength(0);
		
		while ((ch = getch()) != -1 && ch != '>') {
			fTmpBuffer.append((char)ch);
		}
         		
		if (ch != '>') {
			throw new DBFormatException("Unterminated SDB record");
		}

		// Trim off the version number, if present
		int base_end = fTmpBuffer.indexOf("::");
		if (base_end != -1) {
			fTmpBuffer.setLength(base_end);
		}
		
		return fTmpBuffer.toString();
	}
	
	public Enum readEnumType(Class enum_type) throws DBFormatException {
		List<Enum> enum_vals = fEnumMap.get(enum_type);
		String type = readTypeString();
		
		if (!"ET".equals(type)) {
			throw new DBFormatException(
					"Bad format for enum type: \"" + type + "\"");
		}
		
		int ch;
		int idx;
		
		if ((ch = getch()) != '<') { // expect '<'
			throw new DBFormatException("Missing '<' on item-list size (" + (char)ch + ")"); 
		}

		idx = readRawInt();
		
		if ((ch = getch()) != '>') {
			throw new DBFormatException("Missing '>' on item-list size");
		}

		return enum_vals.get(idx);
	}
	
	public int readInt() throws DBFormatException {
		String type = readTypeString();
		
		if (!"I".equals(type)) {
			throw new DBFormatException(
					"Bad format for integer: \"" + type + "\"");
		}
		
		int ch = getch(); // expect '<'
		
		
		int ret = readRawHexInt();
		
		if ((ch = getch()) != '>') { // expect '>'
			throw new DBFormatException(
					"Unterminated integer: \"" + (char)ch + "\"");
		}

		return ret;
	}

	public List<Integer> readIntList() throws DBFormatException {
		String type = readTypeString();
		
		if (!"SNL".equals(type)) {
			throw new DBFormatException(
					"Bad format for integer-list: \"" + type + "\"");
		}
		
		int ch;
		int size;
		
		if ((ch = getch()) != '<') { // expect '<'
			throw new DBFormatException(
					"Bad format for string-list: expecting '<' (" + (char)ch + ")");
		}
		
		size = readRawInt();
		
		ch = getch(); // expect '>'
		
		if (size == -1) {
			return null;
		} else {
			List<Integer> ret = new ArrayList<Integer>();

			while (size-- > 0) {
				ret.add(readInt());
			}
			
			return ret;
		}
	}

	public List readItemList(SVDBFile file, SVDBScopeItem parent)
			throws DBFormatException {
		String type = readTypeString();
		
		if (!"SIL".equals(type)) {
			throw new DBFormatException(
					"Bad format for item list: \"" + type + "\"");
		}
		
		int ch;
		int size;
		
		if ((ch = getch()) != '<') { // expect '<'
			throw new DBFormatException("Missing '<' on item-list size (" + (char)ch + ")"); 
		}

		size = readRawInt();
		
		if ((ch = getch()) != '>') {
			throw new DBFormatException("Missing '>' on item-list size");
		}
		
		if (size == -1) {
			return null;
		} else {
			List<SVDBItem> ret = new ArrayList<SVDBItem>();
			while (size-- > 0) {
				ret.add((SVDBItem)readSVDBItem(file, parent));
			}
			
			return ret;
		}
	}

	public SVDBItemType readItemType() throws DBFormatException {
		return (SVDBItemType)readEnumType(SVDBItemType.class);
/*
		String type = readTypeString();
		
		if (!"IT".equals(type)) {
			throw new DBFormatException(
					"Bad format for item type: \"" + type + "\"");
		}
		
		int ch = getch();
		
		fTmpBuffer.setLength(0);
		
		while ((ch = getch()) != -1 && ch != '>') {
			fTmpBuffer.append((char)ch);
		}
		
		if (ch != '>') {
			throw new DBFormatException(
					"Unterminated item type: \"" + (char)ch + "\"");
		}
		
		SVDBItemType ret = null;
		
		try {
			ret = SVDBItemType.valueOf(fTmpBuffer.toString());
		} catch (Exception e) {
			System.out.println("[ERROR] value \"" + fTmpBuffer.toString() + "\" isn't an SVDBItemType value");
		}
		
		return ret;
 */		
	}

	public long readLong() throws DBFormatException {
		String type = readTypeString();
		
		if (!"L".equals(type)) {
			throw new DBFormatException(
					"Bad format for long: \"" + type + "\"");
		}
		
		int ch = getch();
		
		fTmpBuffer.setLength(0);
		
		while ((ch = getch()) != -1 && ch != '>') {
			fTmpBuffer.append((char)ch);
		}
		
		if (ch != '>') {
			throw new DBFormatException(
					"Unterminated integer: \"" + (char)ch + "\"");
		}
		
		return Long.parseLong(fTmpBuffer.toString(), 16);
	}

	public String readString() throws DBFormatException {
		String type = readTypeString();
		
		if (!"S".equals(type)) {
			throw new DBFormatException(
					"Bad format for string: \"" + type + "\"");
		}
		
		int ch;
		
		// Expect the next char to be '<' as well
		if ((ch = getch()) != '<') {
			throw new DBFormatException("STRING");
		}
		
		fTmpBuffer.setLength(0);
		
		ch = getch(); // expect '<'
		
		int size = readRawInt();
		
		if ((ch = getch()) != '>') {
			throw new DBFormatException(
					"Unterminated string size: \"" + (char)ch + "\"");
		}
		
		if (size == -1) {
			if ((ch = getch()) != '>') {
				throw new DBFormatException("Unterminated null string");
			}
			return null;
		} else {
			fTmpBuffer.setLength(0);
			while ((ch = getch()) != -1 && size-- > 0) {
				fTmpBuffer.append((char)ch);
			}

			// if ((ch = getch()) != '>') {
			if (ch != '>') {
				System.out.println("string thus far is: " + 
						fTmpBuffer.toString());
				throw new DBFormatException(
						"Unterminated string: \"" + (char)ch + "\"");
			}

			return fTmpBuffer.toString();
		}
	}

	public byte [] readByteArray() throws DBFormatException {
		byte ret[] = null;

		String type = readTypeString();
		
		if (!"BA".equals(type)) {
			throw new DBFormatException(
					"Bad format for byte array : \"" + type + "\"");
		}
		
		int ch;
		
		// Expect the next char to be '<' as well
		if ((ch = getch()) != '<') {
			throw new DBFormatException("BYTE_ARRAY");
		}
		
		fTmpBuffer.setLength(0);
		
		ch = getch(); // expect '<'
		
		int size = readRawInt();
		
		if ((ch = getch()) != '>') {
			throw new DBFormatException(
					"Unterminated bytearray size: \"" + (char)ch + "\"");
		}
		
		if (size == -1) {
			if ((ch = getch()) != '>') {
				throw new DBFormatException("Unterminated null string");
			}
		} else if (size == 0) {
			// Expect a closing '>'
			if ((ch = getch()) != '>') {
				throw new DBFormatException("Unterminated empty byte array");
			}
		} else {
			ret = new byte[size];
			
			for (int i=0; i<size; i++) {
				fTmpBuffer.setLength(0);
				while ((ch = getch()) != -1 && ch != ',' && ch != '>') {
					fTmpBuffer.append((char)ch);
				}
				
				try {
					ret[i] = Byte.parseByte(fTmpBuffer.toString());
				} catch (NumberFormatException e) {
					throw new DBFormatException("Failed to parse byteArray element \"" + 
							fTmpBuffer.toString() + "\": " + e.getMessage());
				}
			}

			if (ch != '>') {
				throw new DBFormatException(
						"Unterminated byteArray: \"" + (char)ch + "\"");
			}
		}
		
		return ret;
	}

	public List<String> readStringList() throws DBFormatException {
		String type = readTypeString();
		
		if (!"SSL".equals(type)) {
			throw new DBFormatException(
					"Bad format for string-list: \"" + type + "\"");
		}
		
		int ch;
		int size;
		
		if ((ch = getch()) != '<') { // expect '<'
			throw new DBFormatException(
					"Bad format for string-list: expecting '<' (" + (char)ch + ")");
		}
		
		size = readRawInt();
		
		/* ch = */ getch(); // expect '>'
		
		if (size == -1) {
			return null;
		} else {
			List<String> ret = new ArrayList<String>();

			while (size-- > 0) {
				ret.add(readString());
			}
			
			return ret;
		}
	}

	private int readRawInt() throws DBFormatException {
		int ret = 0;
		int ch;
		
		if ((ch = getch()) == '-') {
			if ((ch = getch()) == '1') {
				return -1;
			} else {
				throw new DBFormatException("Only -1 is supported as negative number");
			}
		} else {
			unget(ch);
			
			while ((ch = getch()) != -1 && ch >= '0' && ch <= '9') {
				ret *= 10;
				ret += (ch - '0');
			}
			
			unget(ch);
			
		}
		
		return ret;
	}
	
	private int readRawHexInt() throws DBFormatException {
		int ret = 0;
		int ch;
		
		if ((ch = getch()) == '-') {
			if ((ch = getch()) == '1') {
				return -1;
			} else {
				throw new DBFormatException("Only -1 is supported as negative number");
			}
		} else {
			unget(ch);
			
			while ((ch = getch()) != -1 && 
					((ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f'))) {
				ret *= 16;
				if ((ch >= '0' && ch <= '9')) {
					ret += (ch - '0');
				} else {
					ret += (10 + (ch - 'a'));
				}
			}
			
			unget(ch);
			
			return ret;
		}
	}
	
	public SVDBItemBase readSVDBItem(
			SVDBFile			file,
			SVDBScopeItem		parent
			) throws DBFormatException {
		SVDBItemBase ret = null;
		
		SVDBItemType type   = readItemType();
		
		if (type == SVDBItemType.NULL) {
			return null;
		} else if (fSVDBFactoryMap.containsKey(type)) {
			ret = fSVDBFactoryMap.get(type).readSVDBItem(this, type, file, parent);
		} else {
			throw new DBFormatException("Unsupported SVDBItemType " + type);
		}
		
		return ret;
	}

	public String readTypeString() {
		fTmpBuffer.setLength(0);
		
		int ch;
		int count = 0;
		
		while ((ch = getch()) != -1 && ch != '<' && ++count < 16) {
			fTmpBuffer.append((char)ch);
		}
		
		if (ch == '<') {
			unget(ch);
			return fTmpBuffer.toString();
		} else {
			return null;
		}
	}

	public int getch() {
		int ch = -1;
		
		if (fUngetCh != -1) {
			ch = fUngetCh;
			fUngetCh = -1;
		} else {
			if (fBufIdx >= fBufSize) {
				try {
					fBufSize = fIn.read(fBuf, 0, fBuf.length);
					fBufIdx  = 0;
				} catch (IOException e) { }
			}
			
			if (fBufIdx < fBufSize) {
				ch = fBuf[fBufIdx++];
			}
		}
		
		return ch;
	}
	
	public void unget(int ch) {
		fUngetCh = ch;
	}
}

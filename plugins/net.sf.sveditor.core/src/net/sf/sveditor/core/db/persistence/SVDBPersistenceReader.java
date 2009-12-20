package net.sf.sveditor.core.db.persistence;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBCoverPoint;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBPreProcCond;
import net.sf.sveditor.core.db.SVDBProgramBlock;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;

public class SVDBPersistenceReader implements IDBReader {
	private InputStream			fIn;
	private byte				fBuf[];
	private int					fBufIdx;
	private int					fBufSize;
	private int					fUngetCh;
	private StringBuilder		fTmpBuffer;

	
	
	public SVDBPersistenceReader(InputStream in) {
		fIn      	= in;
		fBuf     	= new byte[1024*1024];
		fBufIdx  	= 0;
		fBufSize 	= 0;
		fUngetCh	= -1;
		fTmpBuffer 	= new StringBuilder();
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

	@SuppressWarnings("unchecked")
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
			List ret = new ArrayList();
			while (size-- > 0) {
				ret.add(readSVDBItem(file, parent));
			}
			
			return ret;
		}
	}

	public SVDBItemType readItemType() throws DBFormatException {
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
		
		ch = getch(); // expect '>'
		
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
	
	private SVDBItem readSVDBItem(
			SVDBFile			file,
			SVDBScopeItem		parent
			) throws DBFormatException {
		SVDBItem ret = null;
		
		SVDBItemType type   = readItemType();
		
		switch (type) {
			case Class:
				ret = new SVDBModIfcClassDecl(file, parent, type, this);
				break;
				
			case Program:
				ret = new SVDBProgramBlock(file, parent, type, this);
				break;
				
			case Covergroup:
				ret = new SVDBCoverGroup(file, parent, type, this);
				break;
				
			case Coverpoint:
				ret = new SVDBCoverPoint(file, parent, type, this);
				break;
				
			case CoverpointCross:
				ret = new SVDBCoverpointCross(file, parent, type, this);
				break;
				
			case File:
				ret = new SVDBFile(file, parent, type, this);
				break;
				
			case Function:
				ret = new SVDBTaskFuncScope(file, parent, type, this);
				break;
				
			case Include:
				ret = new SVDBInclude(file, parent, type, this);
				break;
				
			case Interface:
				ret = new SVDBModIfcClassDecl(file, parent, type, this);
				break;
				
			case Macro:
				ret = new SVDBMacroDef(file, parent, type, this);
				break;
				
			case ModIfcClassParam:
				ret = new SVDBModIfcClassParam(file, parent, type, this);
				break;
				
			case ModIfcInst:
				ret = new SVDBModIfcInstItem(file, parent, type, this);
				break;
				
			case Module:
				ret = new SVDBModIfcClassDecl(file, parent, type, this);
				break;
				
			case PackageDecl:
				ret = new SVDBPackageDecl(file, parent, type, this);
				break;
				
			case PreProcCond:
				ret = new SVDBPreProcCond(file, parent, type, this);
				break;
				
			case Property:
				ret = new SVDBScopeItem(file, parent, type, this);
				break;
				
			case Sequence:
				ret = new SVDBScopeItem(file, parent, type, this);
				break;
				
			case Struct:
				ret = new SVDBModIfcClassDecl(file, parent, type, this);
				break;
				
			case Task:
				ret = new SVDBTaskFuncScope(file, parent, type, this);
				break;
				
			case TaskFuncParam:
				ret = new SVDBTaskFuncParam(file, parent, type, this);
				break;
				
			case VarDecl:
				ret = new SVDBVarDeclItem(file, parent, type, this);
				break;
				
			case Constraint:
				ret = new SVDBConstraint(file, parent, type, this);
				break;
				
			case Typedef: 
				ret = new SVDBTypedef(file, parent, type, this);
				break;
				
			default:
				System.out.println("[ERROR] unimplemented SVDBLoad type " + type);
				break;
		}
		
		return ret;
	}

	private String readTypeString() {
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

	private int getch() {
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
	
	private void unget(int ch) {
		fUngetCh = ch;
	}
}

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
package org.eclipse.hdt.sveditor.core.argfile.filter;

import java.io.OutputStream;
import java.io.PrintStream;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileLibExtStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;

public class ArgFileWriter {
	private PrintStream				fPS;
	
	public void write(SVDBFile file, OutputStream out) {
		
		fPS = new PrintStream(out);
		
		for (ISVDBChildItem item : file.getChildren()) {
			write(item);
			
		}
		
		fPS.flush();
	}
	
	protected void writeDefineStmt(SVDBArgFileDefineStmt stmt) {
		if (stmt.getValue() == null || stmt.getValue().trim().equals("")) {
			fPS.println("+define+" + stmt.getKey());
		} else {
			fPS.println("+define+" + stmt.getKey() + "=" + stmt.getValue());
		}
	}
	
	protected void writeIncDirStmt(SVDBArgFileIncDirStmt stmt) {
		fPS.println("+incdir+" + stmt.getIncludePath());
	}
	
	protected void writeIncFileStmt(SVDBArgFileIncFileStmt stmt) {
		if (stmt.isRootInclude()) {
			fPS.println("-F " + stmt.getPath());
		} else {
			fPS.println("-f " + stmt.getPath());
		}
	}
	
	protected void writeLibExtStmt(SVDBArgFileLibExtStmt stmt) {
		// TODO:
	}
	
	protected void writePathStmt(SVDBArgFilePathStmt stmt) {
		fPS.println(stmt.getPath());
	}
	
	protected void writeSrcLibPathStmt(SVDBArgFileSrcLibPathStmt stmt) {
		fPS.println("-y " + stmt.getSrcLibPath());
	}
	
	private void write(ISVDBChildItem item) {
		switch (item.getType()) {
			case ArgFileDefineStmt: {
				writeDefineStmt((SVDBArgFileDefineStmt)item);
			} break;
			
			case ArgFileIncDirStmt: {
				writeIncDirStmt((SVDBArgFileIncDirStmt)item);
			} break;
			
			case ArgFileIncFileStmt: {
				writeIncFileStmt((SVDBArgFileIncFileStmt)item);
			} break;
			
			case ArgFileForceSvStmt: {
//				writeForceSvStmt((SVDB))
			} break;
			
			case ArgFileLibExtStmt: {
				writeLibExtStmt((SVDBArgFileLibExtStmt)item);
			} break;
			
			case ArgFilePathStmt: {
				writePathStmt((SVDBArgFilePathStmt)item);
			} break;
			
			case ArgFileSrcLibPathStmt: {
				writeSrcLibPathStmt((SVDBArgFileSrcLibPathStmt)item);
			} break;
			
			case ArgFileMfcuStmt: {
				fPS.println("-mfcu");
			} break;
			
			default: {
				fPS.println("// [ERROR] Unknown argument file statement: " + item.getType());
			}
		}
	}

}

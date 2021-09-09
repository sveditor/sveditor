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

public class ScriptMessageScannerDescriptor {
	public enum ScannerType {
		General,
		Build,
		Run
	}
	
	private String							fId;
	private String							fName;
	private ScannerType						fType;
	private ILogMessageScanner				fScanner;
	
	public ScriptMessageScannerDescriptor(
			String						id,
			String						name,
			ScannerType					type,
			ILogMessageScanner			scanner) {
		fId = id;
		fName = name;
		fType = type;
		fScanner = scanner;
	}
	
	public ILogMessageScanner getScanner() {
		return fScanner;
	}
	
	public String getId() {
		return fId;
	}
	
	public String getName() {
		return fName;
	}
	
	public ScannerType getType() {
		return fType;
	}
	
}

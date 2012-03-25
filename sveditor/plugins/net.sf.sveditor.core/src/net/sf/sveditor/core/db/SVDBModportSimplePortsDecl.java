/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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
import java.util.List;

public class SVDBModportSimplePortsDecl extends SVDBModportPortsDecl {
	public enum PortDir {
		input,
		output,
		inout
	};
	public PortDir							fPortDir;
	public List<SVDBModportSimplePort>		fPortList;
	
	public SVDBModportSimplePortsDecl() {
		super(SVDBItemType.ModportSimplePortsDecl);
		fPortList = new ArrayList<SVDBModportSimplePort>();
	}
	
	public void setPortDir(PortDir dir) {
		fPortDir = dir;
	}
	
	public void setPortDir(String dir) {
		if (dir.equals("input")) {
			setPortDir(PortDir.input);
		} else if (dir.equals("output")) {
			setPortDir(PortDir.output);
		} else {
			setPortDir(PortDir.inout);
		}
	}
	
	public PortDir getPortDir() {
		return fPortDir;
	}
	
	public List<SVDBModportSimplePort> getPortList() {
		return fPortList;
	}
	
	public void addPort(SVDBModportSimplePort port) {
		fPortList.add(port);
	}

}

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
package net.sf.sveditor.core.argfile.parser;

import net.sf.sveditor.core.db.SVDBLocation;

public class SVArgFileToken {
	protected String					fImage;
	protected boolean					fIsPath;
	protected boolean					fIsOption;
	protected String					fOptionVal;
	protected String					fOptionOp;
	protected long						fStartLocation;
	
	public String getImage() {
		return fImage;
	}

	public boolean isPath() {
		return fIsPath;
	}
	
	public boolean isOption() {
		return fIsOption;
	}
	
	public String getOptionVal() {
		return fOptionVal;
	}
	
	public void setOptionVal(String val) {
		fOptionVal = val;
	}
	
	public String getOptionOp() {
		return fOptionOp;
	}
	
	public void setOptionOp(String op) {
		fOptionOp = op;
	}
	
	public long getStartLocation() {
		return fStartLocation;
	}
	
	public SVArgFileToken duplicate() {
		SVArgFileToken ret = new SVArgFileToken();
		ret.fImage = fImage;
		ret.fIsPath = fIsPath;
		ret.fIsOption = fIsOption;
		ret.fStartLocation = fStartLocation;
		ret.fOptionVal = fOptionVal;
		ret.fOptionOp = fOptionOp;
	
		return ret;
	}
}

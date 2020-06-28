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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBMacroDef extends SVDBItem implements ISVDBChildItem {
	public List<SVDBMacroDefParam>			fParams;
	public String							fDef;

	public SVDBMacroDef() {
		super("", SVDBItemType.MacroDef);
	}
	
	public SVDBMacroDef(
			String 				name, 
			String				def) {
		super(name, SVDBItemType.MacroDef);
		fParams = new ArrayList<SVDBMacroDefParam>();
		fDef = def;
	}
	
	public String getDef() {
		return fDef;
	}
	
	public void setDef(String def) {
		fDef = def;
	}
	
	public List<SVDBMacroDefParam> getParameters() {
		return fParams;
	}
	
	public void setParameters(List<SVDBMacroDefParam> params) {
		fParams = params;
		for (SVDBMacroDefParam p : params) {
			p.setParent(this);
		}
	}

	public void addParameter(SVDBMacroDefParam p) {
		fParams.add(p);
		p.setParent(this);
	}
	

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
		
		SVDBMacroDef m = (SVDBMacroDef)other;
		fParams.clear();
		fParams.addAll(m.fParams);
		fDef = m.fDef;
	}

	/*
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBMacroDef) {
			SVDBMacroDef o = (SVDBMacroDef)obj;
			
			if (fParams.size() == o.fParams.size()) {
				 if (!o.fName.equals(fName)) {
					 return false;
				 }
				 
				 for (int i=0; i<fParams.size(); i++) {
					 if (!fParams.get(i).equals(o.fParams.get(i))) {
						 return false;
					 }
				 }

				 return super.equals(obj);
			} else {
				return false;
			}
		}
		
		return false;
	}
	 */
	
}

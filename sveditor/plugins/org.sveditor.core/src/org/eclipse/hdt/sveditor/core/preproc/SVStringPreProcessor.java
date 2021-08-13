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
package org.eclipse.hdt.sveditor.core.preproc;

import java.io.InputStream;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.db.SVDBMacroDef;
import org.eclipse.hdt.sveditor.core.scanner.IPreProcMacroProvider;

public class SVStringPreProcessor implements ISVStringPreProcessor, IPreProcMacroProvider {

	private Map<String, SVDBMacroDef>	fMacroMap;
	private IPreProcMacroProvider		fMacroProvider;
	private boolean						fLocked;
	private boolean						fEmitLineDirectives = true;
	
	public SVStringPreProcessor() {
		fMacroMap = new HashMap<String, SVDBMacroDef>();
		fLocked = false;
	}
	
	public void setLocked(boolean l) {
		fLocked = l;
	}
	
	public SVStringPreProcessor(List<SVDBMacroDef> incoming_macros) {
		fMacroMap = new HashMap<String, SVDBMacroDef>();
		for (SVDBMacroDef m : incoming_macros) {
			addMacro(m);
		}
		fLocked = true;
	}
	
	public SVStringPreProcessor(SVDBMacroDef ... incoming_macros) {
		fMacroMap = new HashMap<String, SVDBMacroDef>();
		for (SVDBMacroDef m : incoming_macros) {
			addMacro(m);
		}
		fLocked = true;
	}
	
	public SVStringPreProcessor(IPreProcMacroProvider macro_provider) {
		fMacroProvider = macro_provider;
		fLocked = true;
	}
	
	public void addListener(IPreProcListener l) {
		// NOP
	}
	
	public void removeListener(IPreProcListener l) {
		// NOP
	}
	
	@Override
	public String preprocess(InputStream in) {
		SVPreProcessor preproc = new SVPreProcessor("", in, null, null);
		preproc.setEmitLineDirectives(fEmitLineDirectives);
		preproc.setMacroProvider(this);
		
		SVPreProcOutput out = preproc.preprocess();
		
		return out.toString();
	}
	
	public void setEmitLineDirectives(boolean emit) {
		fEmitLineDirectives = emit;
	}

	@Override
	public SVDBMacroDef findMacro(String name, int lineno) {
		if (fMacroProvider != null) {
			return fMacroProvider.findMacro(name, lineno);
		} else {
			return fMacroMap.get(name);
		}
	}

	@Override
	public void addMacro(SVDBMacroDef macro) {
		if (!fLocked) {
			if (fMacroProvider != null) {
				fMacroProvider.addMacro(macro);
			} else {
				if (fMacroMap.containsKey(macro.getName())) {
					fMacroMap.remove(macro.getName());
				}
				fMacroMap.put(macro.getName(), macro);
			}
		}
	}

	@Override
	public void setMacro(String key, String value) {
		addMacro(new SVDBMacroDef(key, value));
	}
	
}

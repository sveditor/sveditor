/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - Initial implementation
 *     
 ****************************************************************************/

package net.sf.sveditor.core.docs.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SymbolTable {
	
	private LogHandle fLog ;
	private Map<String,SymbolTableEntry> fSymbolTable ;

	public SymbolTable() {
		fLog = LogFactory.getLogHandle("DocModelFactory") ;
		fSymbolTable = new HashMap<String,SymbolTableEntry>() ;
	}
	
	public void addSymbol(SymbolTableEntry symbol) {
		if(fSymbolTable.containsKey(symbol.getSymbol())) {
			fLog.error(String.format("Duplicate symbol(%s) ignored", symbol.getSymbol())) ;
		} else {
			fSymbolTable.put(symbol.getSymbol(), symbol) ;
		}
	}
	
	public Set<String> getSymbolSet() {
		return fSymbolTable.keySet() ;
	}
	
	public void dumpSymbols() {
		fLog.debug(ILogLevel.LEVEL_MID, "+----------------------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID, "| Symbol table dump") ;
		fLog.debug(ILogLevel.LEVEL_MID, "+----------------------------------------------------------------------------------") ;
		List<String> sortedSymbols = new ArrayList<String>(getSymbolSet()) ;
		Collections.sort(sortedSymbols, String.CASE_INSENSITIVE_ORDER) ;
		for(String symbol: sortedSymbols) {
			fLog.debug(ILogLevel.LEVEL_MID, "|  " + symbol) ; 
		}
		fLog.debug(ILogLevel.LEVEL_MID, "+----------------------------------------------------------------------------------") ;
	}

	public SymbolTableEntry getSymbol(String symbol) {
		return fSymbolTable.get(symbol) ;
	}
	
	public boolean symbolIsValid(String symbol) {
		return fSymbolTable.containsKey(symbol) ;
	}
	
}

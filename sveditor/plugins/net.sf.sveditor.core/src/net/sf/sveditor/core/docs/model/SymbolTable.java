/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import java.io.IOException;
import java.io.Writer;
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
		fLog = LogFactory.getLogHandle("SymbolTable") ;
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
	
	public void dumpSymbolsToFile(Writer writer) throws IOException {
		writer.write("+----------------------------------------------------------------------------------\n") ;
		writer.write("| Symbol table dump\n") ;
		writer.write("+----------------------------------------------------------------------------------\n") ;
		List<String> sortedSymbols = new ArrayList<String>(getSymbolSet()) ;
		Collections.sort(sortedSymbols, String.CASE_INSENSITIVE_ORDER) ;
		for(String symbol: sortedSymbols) {
			writer.write(String.format("|  %s\n", symbol)) ;
			writer.write(String.format("|  		isDocumented(%s)\n", fSymbolTable.get(symbol).isDocumented())) ;
			writer.write(String.format("|  		topicType(%s)\n", fSymbolTable.get(symbol).getTopicType())) ;
			writer.write(String.format("|  		symbolType(%s)\n", fSymbolTable.get(symbol).getSymbolType())) ;
		}
		writer.write("+----------------------------------------------------------------------------------\n") ;
	}

	public SymbolTableEntry getSymbol(String symbol) {
		return fSymbolTable.get(symbol) ;
	}
	
	public boolean symbolIsValid(String symbol) {
		return fSymbolTable.containsKey(symbol) ;
	}

	public SymbolTableEntry resolveSymbol(DocTopic docTopic, String symbol) {
		fLog.debug(ILogLevel.LEVEL_MID, "+----------------------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID,
				String.format("| Resolving(%s) from (%s)", symbol, docTopic.getQualifiedName())) ;
		fLog.debug(ILogLevel.LEVEL_MID, "+----------------------------------------------------------------------------------") ;
		String enclosingScope = docTopic.getQualifiedName() ;
		SymbolTableEntry entry = null ;
		int safetyCount = 0 ; // Watch for infinite loop
		while(true) {
			if(enclosingScope == null) {
				fLog.debug(ILogLevel.LEVEL_MID, "| trying " + symbol) ;
				if(fSymbolTable.containsKey(symbol)) {
					entry = fSymbolTable.get(symbol) ;
					fLog.debug(ILogLevel.LEVEL_MID,
							String.format("| Found(%s)", symbol)) ;
					break ;
				} else {
					/* Before giving up completely, let's get sloppy and look for this 
					 * symbol under any other arbitrary scope
					 */
					entry = sloppySymbolLookup(symbol) ;
					if(entry == null) {
                      fLog.debug(ILogLevel.LEVEL_MID, "| Failed to find symbol") ;
					}
					break ;
				}
			} else {
				String trySymbol = enclosingScope + "::" + symbol ;
				fLog.debug(ILogLevel.LEVEL_MID, "| trying " + trySymbol) ;
				if(fSymbolTable.containsKey(trySymbol)) {
					entry = fSymbolTable.get(trySymbol) ;
					fLog.debug(ILogLevel.LEVEL_MID,
							String.format("| Found(%s)", trySymbol)) ;
					break ;
				}
				int index = enclosingScope.lastIndexOf("::") ;
				if(index != -1) {
					enclosingScope = enclosingScope.substring(0, index) ;
				} else {
					enclosingScope = null ;
				}
			}
			safetyCount++ ;
			if(safetyCount >= 50) {
				fLog.error(String.format("Safety count kicked in while resolving(%s) from (%s)", symbol, docTopic.getQualifiedName())) ;
				break ;
			}
			
		}
		fLog.debug(ILogLevel.LEVEL_MID, "+----------------------------------------------------------------------------------") ;
		return entry ;
	}

	private SymbolTableEntry sloppySymbolLookup(String symbol) {
		SymbolTableEntry entry = null ;
		for(String trySymbol: getSymbolSet()) {
		   String choppedTrySymbol = trySymbol ;
		   int index = choppedTrySymbol.indexOf("::") ;
 		   if(index != -1 && index+2 < choppedTrySymbol.length()) {
					choppedTrySymbol = trySymbol.substring(index+2) ;
					fLog.debug(ILogLevel.LEVEL_MID, "| trying sloppily " + choppedTrySymbol) ;
					if(choppedTrySymbol.matches(symbol)) {
					  entry = fSymbolTable.get(trySymbol) ;
					  fLog.debug(ILogLevel.LEVEL_MID,
							  String.format("| Found(%s) sloppily", trySymbol)) ;
					  break ;
					}
 		   }
			
		}
		return entry ;
	}
	
}

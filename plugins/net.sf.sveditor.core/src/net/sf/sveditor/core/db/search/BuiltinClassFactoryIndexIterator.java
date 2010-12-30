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


package net.sf.sveditor.core.db.search;

import java.util.HashMap;

import net.sf.sveditor.core.BuiltinClassConstants;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

/**
 * Built-in class iterator that constructs SVDB items with appropriate
 * 'built-in' base classes
 * 
 * @author ballance
 *
 */
public class BuiltinClassFactoryIndexIterator implements ISVDBIndexIterator {
	private static final LogHandle				fLog = LogFactory.getLogHandle("BuiltinClassFactoryIndexIterator");
	private ISVDBIndexIterator					fBaseIterator;
	private HashMap<SVDBItem, SVDBItem>			fItemMap;
	
	public BuiltinClassFactoryIndexIterator(ISVDBIndexIterator it) {
		fBaseIterator = it;
		fItemMap = new HashMap<SVDBItem, SVDBItem>();
	}
	
	private class BuiltinClassIterator implements ISVDBItemIterator {
		private ISVDBItemIterator 		fIterator;
		
		public BuiltinClassIterator() {
			fIterator = fBaseIterator.getItemIterator();
		}

		public boolean hasNext(SVDBItemType ... type_list) {
			return fIterator.hasNext(type_list);
		}

		public SVDBItem nextItem(SVDBItemType ... type_list) {
			SVDBItem it = fIterator.nextItem(type_list);
			if (it != null) {
				if (fItemMap.containsKey(it)) {
					it = fItemMap.get(it);
				} else if (BuiltinClassConstants.hasBuiltin(it.getType())) {
					// Create a duplicate item with the correct base type
					SVDBModIfcClassDecl cls = 
						(SVDBModIfcClassDecl)((SVDBModIfcClassDecl)it).duplicate();
					cls.setSuperClass(
							BuiltinClassConstants.getBuiltinClass(it.getType()));
					fLog.debug("Create modified type for " + 
							it.getType() + " " + it.getName() + 
							" super-class=" + BuiltinClassConstants.getBuiltinClass(it.getType()));
					
					// Cache for future efficiency
					fItemMap.put(it, cls);
					it = cls;
				}
			}
			
			return it;
		}
	}

	public ISVDBItemIterator getItemIterator() {
		return new BuiltinClassIterator();
	}

}

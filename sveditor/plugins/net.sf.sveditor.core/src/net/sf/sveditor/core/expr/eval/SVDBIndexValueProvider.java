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


package net.sf.sveditor.core.expr.eval;

import java.math.BigInteger;

import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

public class SVDBIndexValueProvider implements IValueProvider {
	
	private ISVDBIndexIterator				fIndexIt;
	
	public SVDBIndexValueProvider(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
	}

	public BigInteger get_value(String name) throws Exception {
		/** TODO:
		ISVDBItemIterator item_it = fIndexIt.getItemIterator(new NullProgressMonitor());
		
		while (item_it.hasNext()) {
			ISVDBItemBase it = item_it.nextItem();
			
			if (it.getType() == SVDBItemType.TypedefStmt) {
				SVDBTypedefStmt typedef = (SVDBTypedefStmt)it;
				if (typedef.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
					SVDBTypeInfoEnum enum_t = (SVDBTypeInfoEnum)typedef.getTypeInfo();
				
					Tuple<List<String>, List<String>> enums = enum_t.getEnumValues();
					for (int i=0; i<enums.first().size(); i++) {
						String key = enums.first().get(i);
						String val = enums.second().get(i);
						
						if (key.equals(name)) {
							long lv = -1;
							// TODO: parse ? 
							try {
								lv = Long.parseLong(val);
							} catch (NumberFormatException e) {}
							
							return BigInteger.valueOf(lv);
						}
					}
				}
			}
			return BigInteger.ZERO;
		}
				 */
		
		throw new Exception("Unknown value \"" + name + "\"");
	}

}

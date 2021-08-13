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


package org.eclipse.hdt.sveditor.core.expr.eval;

import java.math.BigInteger;

import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;

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

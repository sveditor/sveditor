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

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

public class SVDBIndexValueProvider implements IValueProvider {
	
	private ISVDBIndexIterator				fIndexIt;
	
	public SVDBIndexValueProvider(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
	}

	public BigInteger get_value(String name) throws Exception {
		ISVDBItemIterator item_it = fIndexIt.getItemIterator();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			
			if (it.getType() == SVDBItemType.Typedef) {
				SVDBTypedef typedef = (SVDBTypedef)it;
				if (typedef.getTypeInfo().getDataType() == SVDBDataType.Enum) {
					SVDBTypeInfoEnum enum_t = (SVDBTypeInfoEnum)typedef.getTypeInfo();
				
					for (Tuple<String, String> n : enum_t.getEnumValues()) {
						if (n.first().equals(name)) {
							long lv = -1;
							// TODO: parse ? 
							try {
								lv = Long.parseLong(n.second());
							} catch (NumberFormatException e) {}
							
							return BigInteger.valueOf(lv);
						}
					}
				}
			}
		}
		
		throw new Exception("Unknown value \"" + name + "\"");
	}

}

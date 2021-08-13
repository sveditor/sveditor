/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.db.persistence;

public interface IDBPersistenceTypes {
	int					TYPE_INT_8 			= 0;
	int					TYPE_INT_16			= 1;
	int					TYPE_INT_32			= 2;
	int					TYPE_INT_64			= 3;
	int					TYPE_INT_LIST 		= 4;
	int					TYPE_STRING			= 5;
	int					TYPE_STRING_LIST	= 6;
	int					TYPE_NULL			= 7;
	int					TYPE_ITEM			= 8;
	int					TYPE_ITEM_LIST		= 9;
	int					TYPE_BOOL_FALSE		= 10;
	int					TYPE_BOOL_TRUE		= 11;
	int					TYPE_ENUM			= 12;
	int					TYPE_BYTE_ARRAY		= 13;
	int					TYPE_SVDB_LOCATION	= 14;
	int					TYPE_MAP			= 15;
	int					TYPE_LONG_LIST		= 16;
	int					TYPE_OBJECT_LIST	= 17;
	int					TYPE_STRING_SET		= 18;
	int					TYPE_INT_SET		= 19;
	int					TYPE_LONG_SET		= 20;
	
	int					TYPE_MAX			= 31;
	

}

/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs.model;

public class DocSectionItem extends DocTopic {

	public DocSectionItem(String name, String summary) {
		super(name, DocItemType.PACKAGESECTION) ;
	}

	public DocSectionItem(String title) {
		this(title, "") ;
	}

}

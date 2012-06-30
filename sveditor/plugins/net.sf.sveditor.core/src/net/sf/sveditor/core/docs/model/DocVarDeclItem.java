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

import java.util.ArrayList;

import net.sf.sveditor.core.db.IFieldItemAttr;

public class DocVarDeclItem extends DocItem implements IFieldItemAttr {
	
	public int fFieldAttr ;

	ArrayList<DocTopic> fTopics ;
	public ArrayList<DocTopic> getTopics() {
		return fTopics ;
	}
	
	public void addTopic(DocTopic topic) {
		fTopics.add(topic) ;
	}
	
	public DocVarDeclItem(String name) {
		super(name, DocItemType.VarDeclDoc);
		fTopics = new ArrayList<DocTopic>() ;
	}

	public void setAttr(int attr) {
		fFieldAttr = attr ;
	}

	public int getAttr() {
		return fFieldAttr ;
	}

}

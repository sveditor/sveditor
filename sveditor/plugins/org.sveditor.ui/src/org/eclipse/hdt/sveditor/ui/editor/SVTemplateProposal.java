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
package org.eclipse.hdt.sveditor.ui.editor;

import org.eclipse.hdt.sveditor.ui.SVDBIconUtils;
import org.eclipse.hdt.sveditor.ui.doc.DocUtilUi;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.docs.DocUtil;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.templates.Template;
import org.eclipse.jface.text.templates.TemplateContext;
import org.eclipse.jface.text.templates.TemplateProposal;

public class SVTemplateProposal extends TemplateProposal {
	private ISVDBItemBase		fItem;
	private ISVDBIndexIterator	fIndexIt;
	
	public SVTemplateProposal(
			Template 			template, 
			TemplateContext 	context, 
			IRegion 			region, 
			ISVDBIndexIterator	index_it,
			ISVDBItemBase		item) {
		super(template, context, region, SVDBIconUtils.getIcon(item));
		fIndexIt = index_it;
		fItem = item;
	}

	@Override
	public String getAdditionalProposalInfo() {
		if (fItem != null && fIndexIt != null) {
			String description = DocUtil.getDocComment(fIndexIt, fItem);
			
			if (description != null) {
				description = DocUtilUi.formatDoc(description);
			} else {
				description = "";
			}
			
			return description;			
		} else {
			return null;
		}
	}

}

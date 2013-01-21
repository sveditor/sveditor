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


package net.sf.sveditor.core.content_assist;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;

public class SVCompletionProposal {
	public static final int				PRIORITY_BEHAVIORAL_SCOPE    = 0;
	public static final int				PRIORITY_MOD_IFC_CLS_SCOPE   = (PRIORITY_BEHAVIORAL_SCOPE+1);
	public static final int				PRIORITY_CLS_HIERARCHY_SCOPE = (PRIORITY_MOD_IFC_CLS_SCOPE+1);
	public static final int				PRIORITY_PACKAGE_SCOPE 		 = (PRIORITY_CLS_HIERARCHY_SCOPE+1);
	public static final int				PRIORITY_GLOBAL_SCOPE 		 = (PRIORITY_PACKAGE_SCOPE+1);
	public static final int				PRIORITY_PREPROC_SCOPE 		 = (PRIORITY_GLOBAL_SCOPE+1);
	public static final int				PRIORITY_MAX = (PRIORITY_PREPROC_SCOPE+1);
	
	private ISVDBItemBase				fItem;
	private String						fPrefix;
	private String						fReplacement;
	private int							fReplacementOffset;
	private int							fReplacementLength;
	private SVCompletionProposalType	fType;
	private int							fPriorityCategory;
	private int							fPriority;
	
	
	public SVCompletionProposal(
			ISVDBItemBase 	item,
			String			prefix,
			int				replacementOffset,
			int				replacementLength) {
		fItem 				= item;
		fPrefix 			= prefix;
		fReplacement		= SVDBItem.getName(item);
		fReplacementOffset 	= replacementOffset;
		fReplacementLength 	= replacementLength;
		fType				= SVCompletionProposalType.SVObject;
	}
	
	public void setPriorityCategory(int p) {
		fPriorityCategory = p;
	}
	
	public int getPriorityCategory() {
		return fPriorityCategory;
	}
	
	public void setPriority(int p) {
		fPriority = p;
	}
	
	public int getPriority() {
		return fPriority;
	}
	
	public String getPrefix() {
		return fPrefix;
	}
	
	public String getReplacement() {
		return fReplacement;
	}
	
	public void setReplacement(String replacement) {
		fReplacement = replacement;
	}
	
	public SVCompletionProposal(
			String 				replacement, 
			int 				startOffset, 
			int 				replacementLength) {
		fReplacement 		= replacement;
		fReplacementOffset 	= startOffset;
		fReplacementLength 	= replacementLength;
		fType				= SVCompletionProposalType.Unknown;
	}

	public SVCompletionProposal(
			String 						replacement, 
			int 						startOffset, 
			int 						replacementLength,
			SVCompletionProposalType	type) {
		fReplacement 		= replacement;
		fReplacementOffset 	= startOffset;
		fReplacementLength 	= replacementLength;
		fType				= type;
	}

	public ISVDBItemBase getItem() {
		return fItem;
	}
	
	public SVCompletionProposalType getType() {
		return fType;
	}
	
	public int getReplacementOffset() {
		return fReplacementOffset;
	}
	
	public int getReplacementLength() {
		return fReplacementLength;
	}

}

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


package net.sf.sveditor.core.content_assist;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class SVCompletionProposal {
	public static final int				PRIORITY_BEHAVIORAL_SCOPE    = 0;
	public static final int				PRIORITY_MOD_IFC_CLS_SCOPE   = (PRIORITY_BEHAVIORAL_SCOPE+1);
	public static final int				PRIORITY_CLS_HIERARCHY_SCOPE = (PRIORITY_MOD_IFC_CLS_SCOPE+1);
	public static final int				PRIORITY_PACKAGE_SCOPE 		 = (PRIORITY_CLS_HIERARCHY_SCOPE+1);
	public static final int				PRIORITY_GLOBAL_SCOPE 		 = (PRIORITY_PACKAGE_SCOPE+1);
	public static final int				PRIORITY_PREPROC_SCOPE 		 = (PRIORITY_GLOBAL_SCOPE+1);
	public static final int				PRIORITY_MAX = (PRIORITY_PREPROC_SCOPE+1);

	private SVDBDeclCacheItem			fCacheItem;
	private ISVDBItemBase				fItem;
	private String						fPrefix;
	private String						fReplacement;
	private int							fReplacementOffset;
	private int							fReplacementLength;
	private String						fDisplayString;
	private String						fAdditionalInfo;
	private SVCompletionProposalType	fType;
	private int							fPriorityCategory;
	private int							fPriority;

	// Context where the proposal must be surrounded with ()
	private boolean						fNameMapped; 
	
	
	public SVCompletionProposal(
			SVDBDeclCacheItem 	item,
			String				prefix,
			int					replacementOffset,
			int					replacementLength) {
		fCacheItem			= item;
		fPrefix 			= prefix;
		fReplacement		= item.getName();
		fReplacementOffset 	= replacementOffset;
		fReplacementLength 	= replacementLength;
		fType				= SVCompletionProposalType.SVObject;
	}

	public SVCompletionProposal(
			ISVDBItemBase 		item,
			String				prefix,
			int					replacementOffset,
			int					replacementLength) {
		fItem				= item;
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
	
	public void setNameMapped(boolean name_mapped) {
		fNameMapped = name_mapped;
	}
	
	public boolean getNameMapped() {
		return fNameMapped;
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
	
	public String getDisplayString() {
		return fDisplayString;
	}
	
	public void setDisplayString(String str) {
		fDisplayString = str;
	}
	
	public String getAdditionalInfo() {
		return fAdditionalInfo;
	}
	
	public void setAdditionalInfo(String str) {
		fAdditionalInfo = str;
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
		if (fItem != null) {
			return fItem;
		} else if (fCacheItem != null) {
			fItem = fCacheItem.getSVDBItem();
			return fItem;
		} else {
			return null;
		}
	}
	
	public SVDBDeclCacheItem getCacheItem() {
		return fCacheItem;
	}
	
	public String getName() {
		if (fCacheItem != null) {
			return fCacheItem.getName();
		} else {
			ISVDBItemBase item = getItem();
			if (item != null) {
				return SVDBItem.getName(item);
			} else {
				return fReplacement;
			}
		}
	}
	
	public SVDBItemType getItemType() {
		if (fCacheItem != null) {
			return fCacheItem.getType();
		} else if (fItem != null) {
			return fItem.getType();
		} else {
			return null;
		}
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

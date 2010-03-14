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

import net.sf.sveditor.core.db.SVDBItem;

public class SVCompletionProposal {
	
	private SVDBItem				fItem;
	private String					fPrefix;
	private String					fReplacement;
	private int						fReplacementOffset;
	private int						fReplacementLength;
	
	public SVCompletionProposal(
			SVDBItem 		item,
			String			prefix,
			int				replacementOffset,
			int				replacementLength) {
		fItem 				= item;
		fPrefix 			= prefix;
		fReplacement		= item.getName();
		fReplacementOffset 	= replacementOffset;
		fReplacementLength 	= replacementLength;
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
	}
	
	public SVDBItem getItem() {
		return fItem;
	}
	
	public int getReplacementOffset() {
		return fReplacementOffset;
	}
	
	public int getReplacementLength() {
		return fReplacementLength;
	}

}

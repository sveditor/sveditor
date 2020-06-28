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
package net.sf.sveditor.core.argfile.content_assist;


public class SVArgFileCompletionProposal {
	
	private String				fPrefix;
	private String				fReplacement;
	private int					fReplacementOffset;
	private int					fReplacementLength;

	public SVArgFileCompletionProposal(
			String			prefix,
			String			replacement,
			int				replacementOffset,
			int				replacementLength) {
		fPrefix 			= prefix;
		fReplacement 		= replacement;
		fReplacementOffset 	= replacementOffset;
		fReplacementLength 	= replacementLength;
	}
	
	public String getPrefix() {
		return fPrefix;
	}
	
	public String getReplacement() {
		return fReplacement;
	}
	
	public int getReplacementOffset() {
		return fReplacementOffset;
	}
	
	public int getReplacementLength() {
		return fReplacementLength;
	}
}

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


package net.sf.sveditor.core.parser;

public class SVToken_sav {
	enum Type {
		Id,
		Keyword,
		String,    // "quoted string"
		Hash,      // #
		LParen,    // (
		RParen,    // )
		Semicolon, // ;
		Comma,     // ,
		Period,    // .
		Colon,     // :
		Equals,    // =
	};
	
	private String				fImage;
	private Type				fType;
	
	
	public SVToken_sav(Type type, String image) {
		fType  = type;
		fImage = image;
	}
	
	public boolean isKeyword(String kw) {
		return (fImage.equals(kw));
	}

	public String getImage() {
		return fImage;
	}
	
	public Type getType() {
		return fType;
	}

}

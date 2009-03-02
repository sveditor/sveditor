package net.sf.sveditor.core.parser;

public class SVToken {
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
	
	
	public SVToken(Type type, String image) {
		fType  = type;
		fImage = image;
	}

	public SVKeywords getKeyword() {
		return SVKeywords.getKeyword(fImage);
	}
	
	public String getImage() {
		return fImage;
	}
	
	public Type getType() {
		return fType;
	}

}

package net.sf.sveditor.core.parser;

public class SVParsers {
	
	private ParserSVDBFileFactory			fSVParser;
	private SVClassDeclParser				fClassParser;
	private SVParameterDeclParser			fParamDeclParser;
	private SVParameterPortListParser		fParamPortParser;
	private SVDataTypeParser				fDataTypeParser;
	private SVFunctionParser				fFunctionParser;
	private SVTaskFunctionPortListParser	fTFPortListParser;
	private SVTaskFuncBodyParser			fTFBodyParser;
	private SVBlockItemDeclParser			fBlockItemDeclParser;
	
	public SVParsers(ParserSVDBFileFactory sv_parser) {
		fSVParser = sv_parser;
	}
	
	public ParserSVDBFileFactory SVParser() {
		return fSVParser;
	}
	
	public SVClassDeclParser classParser() {
		if (fClassParser == null) {
			fClassParser = new SVClassDeclParser(fSVParser);
		}
		return fClassParser;
	}
	
	public SVParameterDeclParser paramDeclParser() {
		if (fParamDeclParser == null) {
			fParamDeclParser = new SVParameterDeclParser(fSVParser);
		}
		return fParamDeclParser;
	}
	
	public SVParameterPortListParser paramPortListParser() {
		if (fParamPortParser == null) {
			fParamPortParser = new SVParameterPortListParser(fSVParser);
		}
		return fParamPortParser;
	}
	
	public SVDataTypeParser dataTypeParser() {
		if (fDataTypeParser == null) {
			fDataTypeParser = new SVDataTypeParser(fSVParser);
		}
		return fDataTypeParser;
	}
	
	public SVFunctionParser functionParser() {
		if (fFunctionParser == null) {
			fFunctionParser = new SVFunctionParser(fSVParser);
		}
		return fFunctionParser;
	}
	
	public SVTaskFunctionPortListParser tfPortListParser() {
		if (fTFPortListParser == null) {
			fTFPortListParser = new SVTaskFunctionPortListParser(fSVParser);
		}
		return fTFPortListParser;
	}
	
	public SVTaskFuncBodyParser tfBodyParser() {
		if (fTFBodyParser == null) {
			fTFBodyParser = new SVTaskFuncBodyParser(fSVParser);
		}
		return fTFBodyParser;
	}
	
	public SVBlockItemDeclParser blockItemDeclParser() {
		if (fBlockItemDeclParser == null) {
			fBlockItemDeclParser = new SVBlockItemDeclParser(fSVParser);
		}
		return fBlockItemDeclParser;
	}

}

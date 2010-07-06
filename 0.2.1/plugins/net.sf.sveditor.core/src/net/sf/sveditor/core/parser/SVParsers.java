package net.sf.sveditor.core.parser;

/**
 * Collects the various SVParser classes together to provide easy access
 * 
 * @author ballance
 *
 */
public class SVParsers {
	
	private ParserSVDBFileFactory				fSVParser;
	private SVClassDeclParser					fClassParser;
	private SVParameterDeclParser				fParamDeclParser;
	private SVParameterPortListParser			fParamPortParser;
	private SVDataTypeParser					fDataTypeParser;
	private SVTaskFunctionParser				fFunctionParser;
	private SVTaskFunctionPortListParser		fTFPortListParser;
	private SVTaskFuncBodyParser				fTFBodyParser;
	private SVBlockItemDeclParser				fBlockItemDeclParser;
	private SVParameterValueAssignmentParser	fParamValueAssignParser;
	private SVBehavioralBlockParser				fBehavioralBlockParser;
	
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
	
	public SVTaskFunctionParser functionParser() {
		if (fFunctionParser == null) {
			fFunctionParser = new SVTaskFunctionParser(fSVParser);
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
	
	public SVParameterValueAssignmentParser paramValueAssignParser() {
		if (fParamValueAssignParser == null) {
			fParamValueAssignParser = new SVParameterValueAssignmentParser(fSVParser);
		}
		return fParamValueAssignParser;
	}
	
	public SVBehavioralBlockParser behavioralBlockParser() {
		if (fBehavioralBlockParser == null) {
			fBehavioralBlockParser = new SVBehavioralBlockParser(fSVParser);
		}
		return fBehavioralBlockParser;
	}

}

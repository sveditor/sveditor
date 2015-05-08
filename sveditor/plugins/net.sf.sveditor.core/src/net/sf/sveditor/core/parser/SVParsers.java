/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;


/**
 * Collects the various SVParser classes together to provide easy access
 * 
 * @author ballance
 *
 */
public class SVParsers {
	
	private ISVParser							fSVParser;
	private SVParser				fSVDBFileFactory;
	private SVCommonParserUtils					fCommonParserUtils;
	private SVClassDeclParser					fClassParser;
	private SVCovergroupParser					fCovergroupParser;
	private SVParameterDeclParser				fParamDeclParser;
	private SVParameterPortListParser			fParamPortParser;
	private SVDataTypeParser					fDataTypeParser;
	private SVTaskFunctionParser				fFunctionParser;
	private SVTaskFunctionPortListParser		fTFPortListParser;
	private SVTaskFuncBodyParser				fTFBodyParser;
	private SVBlockItemDeclParser				fBlockItemDeclParser;
	private SVParameterValueAssignmentParser	fParamValueAssignParser;
	private SVBehavioralBlockParser				fBehavioralBlockParser;
	private SVModIfcProgDeclParser				fModIfcProgParser;
	private SVPortListParser					fPortListParser;
	private SVGenerateBlockParser				fGenBlockParser;
	private SVClockingBlockParser				fClkBlockParser;
	private SVSpecifyBlockParser				fSpecifyBlockParser;
	private SVImpExpStmtParser					fImportParser;
	private SVExprParser						fExprParser;
	private SVGateInstantiationParser			fGateInstanceParser;
	private SVAssertionParser					fAssertionParser;
	private SVModIfcBodyItemParser				fModIfcBodyItemParser;
	private SVConstraintParser					fConstraintParser;
	private SVAttributeParser					fAttrParser;
	private boolean_abbrev_or_array_deref				fPropertyExprParser;
	private SVSequenceParser					fSequenceParser;
	private SVPropertyParser					fPropertyParser;
	private SVConfigParser						fConfigParser;
	
	public SVParsers() {
	}
	
	public SVParsers(ISVParser parser) {
		fSVParser = parser;
	}
	
	public void init(SVParser sv_parser) {
		fSVDBFileFactory = sv_parser;
		init((ISVParser)sv_parser);
	}
	
	public void init(ISVParser parser) {
		fSVParser = parser;
		fCommonParserUtils = new SVCommonParserUtils(fSVParser);
		fClassParser = new SVClassDeclParser(fSVParser);
		fParamDeclParser = new SVParameterDeclParser(fSVParser);
		fParamPortParser = new SVParameterPortListParser(fSVParser);
		fDataTypeParser = new SVDataTypeParser(fSVParser);
		fFunctionParser = new SVTaskFunctionParser(fSVParser);
		fTFPortListParser = new SVTaskFunctionPortListParser(fSVParser);
		fTFBodyParser = new SVTaskFuncBodyParser(fSVParser);
		fBlockItemDeclParser = new SVBlockItemDeclParser(fSVParser);
		fParamValueAssignParser = new SVParameterValueAssignmentParser(fSVParser);
		fBehavioralBlockParser = new SVBehavioralBlockParser(fSVParser);
		fModIfcProgParser = new SVModIfcProgDeclParser(fSVParser);
		fPortListParser = new SVPortListParser(fSVParser);
		fGenBlockParser = new SVGenerateBlockParser(fSVParser);
		fClkBlockParser = new SVClockingBlockParser(fSVParser);
		fSpecifyBlockParser = new SVSpecifyBlockParser(fSVParser);
		fImportParser = new SVImpExpStmtParser(fSVParser);
		fExprParser = new SVExprParser(fSVParser);
		fGateInstanceParser = new SVGateInstantiationParser(fSVParser);
		fAssertionParser = new SVAssertionParser(fSVParser);
		fCovergroupParser = new SVCovergroupParser(fSVParser);
		fModIfcBodyItemParser = new SVModIfcBodyItemParser(fSVParser);
		fConstraintParser = new SVConstraintParser(fSVParser);
		fAttrParser = new SVAttributeParser(fSVParser);
		fPropertyExprParser = new boolean_abbrev_or_array_deref(fSVParser);
		fSequenceParser = new SVSequenceParser(fSVParser);
		fPropertyParser = new SVPropertyParser(fSVParser);
		fConfigParser = new SVConfigParser(fSVParser);
	}
	
	public SVParser SVParser() {
		return fSVDBFileFactory;
	}
	
	public SVCommonParserUtils commonParserUtils() {
		return fCommonParserUtils;
	}
	
	public final SVClassDeclParser classParser() {
		return fClassParser;
	}
	
	public SVParameterDeclParser paramDeclParser() {
		return fParamDeclParser;
	}
	
	public SVParameterPortListParser paramPortListParser() {
		return fParamPortParser;
	}
	
	public SVDataTypeParser dataTypeParser() {
		return fDataTypeParser;
	}
	
	public SVTaskFunctionParser taskFuncParser() {
		return fFunctionParser;
	}
	
	public SVTaskFunctionPortListParser tfPortListParser() {
		return fTFPortListParser;
	}
	
	public SVTaskFuncBodyParser tfBodyParser() {
		return fTFBodyParser;
	}
	
	public SVBlockItemDeclParser blockItemDeclParser() {
		return fBlockItemDeclParser;
	}
	
	public SVParameterValueAssignmentParser paramValueAssignParser() {
		return fParamValueAssignParser;
	}
	
	public SVBehavioralBlockParser behavioralBlockParser() {
		return fBehavioralBlockParser;
	}
	
	public SVModIfcProgDeclParser modIfcProgParser() {
		return fModIfcProgParser;
	}
	
	public SVPortListParser portListParser() {
		return fPortListParser;
	}
	
	public SVGenerateBlockParser generateBlockParser() {
		return fGenBlockParser;
	}
	
	public SVClockingBlockParser clockingBlockParser() {
		return fClkBlockParser;
	}
	
	public SVSpecifyBlockParser specifyBlockParser() {
		return fSpecifyBlockParser;
	}
	
	public SVImpExpStmtParser impExpParser() {
		return fImportParser;
	}
	
	public SVExprParser exprParser() {
		return fExprParser;
	}
	
	public SVGateInstantiationParser gateInstanceParser() {
		return fGateInstanceParser;
	}
	
	public SVAssertionParser assertionParser() {
		return fAssertionParser;
	}
	
	public SVCovergroupParser covergroupParser() {
		return fCovergroupParser;
	}
	
	public SVModIfcBodyItemParser modIfcBodyItemParser() {
		return fModIfcBodyItemParser;
	}
	
	public SVConstraintParser constraintParser() {
		return fConstraintParser;
	}
	
	public SVAttributeParser attrParser() {
		return fAttrParser;
	}

	public boolean_abbrev_or_array_deref propertyExprParser() {
		return fPropertyExprParser;
	}

	public SVSequenceParser sequenceParser() {
		return fSequenceParser;
	}
	
	public SVPropertyParser propertyParser() {
		return fPropertyParser;
	}

	public SVConfigParser configParser() {
		return fConfigParser;
	}
}

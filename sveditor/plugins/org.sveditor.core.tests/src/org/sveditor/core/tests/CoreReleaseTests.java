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


package org.sveditor.core.tests;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.log.ILogHandle;
import org.sveditor.core.log.ILogListener;
import org.sveditor.core.log.LogFactory;

import junit.framework.Test;
import junit.framework.TestResult;
import junit.framework.TestSuite;
import org.sveditor.core.tests.argfile.content_assist.ArgFileContentAssistTests;
import org.sveditor.core.tests.argfile.creator.TestArgFileCreator;
import org.sveditor.core.tests.argfile.open_decl.ArgFileOpenDeclTests;
import org.sveditor.core.tests.argfile.parser.ArgFileParserTests;
import org.sveditor.core.tests.content_assist.ContentAssistTests;
import org.sveditor.core.tests.db.SVDBTests;
import org.sveditor.core.tests.docs.DocsTests;
import org.sveditor.core.tests.fileset.FileSetTests;
import org.sveditor.core.tests.hierarchy.HierarchyTests;
import org.sveditor.core.tests.indent.IndentTests;
import org.sveditor.core.tests.index.IndexTests;
import org.sveditor.core.tests.index.argfile2.ArgFileIndex2Tests;
import org.sveditor.core.tests.index.cache.IndexCacheTests;
import org.sveditor.core.tests.index.persistence.PersistenceTests;
import org.sveditor.core.tests.index.refs.IndexRefTests;
import org.sveditor.core.tests.job_mgr.JobMgrTests;
import org.sveditor.core.tests.logscanner.LogScannerTests;
import org.sveditor.core.tests.open_decl.OpenDeclTests;
import org.sveditor.core.tests.parser.ParserTests;
import org.sveditor.core.tests.parser.ams.ParserAMSTests;
import org.sveditor.core.tests.parser.db.ParserDBTests;
import org.sveditor.core.tests.preproc.PreProcTests;
import org.sveditor.core.tests.primitives.PrimitivesTests;
import org.sveditor.core.tests.project_settings.ProjectSettingsTests;
import org.sveditor.core.tests.scanner.PreProcMacroTests;
import org.sveditor.core.tests.searchutils.SearchUtilsTests;
import org.sveditor.core.tests.srcgen.SrcGenTests;

public class CoreReleaseTests extends TestSuite {
	
	private static List<Exception>		fErrors = new ArrayList<Exception>();
	private static ILogListener		fErrorLogListener;
	
	static {
		fErrorLogListener = new ILogListener() {
			public void message(ILogHandle handle, int type, int level, String message) {
				if (type == ILogListener.Type_Error) {
//					System.out.println("MSG: " + message);
					try {
						throw new Exception("[" + handle.getName() + "] " + message);
					} catch (Exception e) {
						fErrors.add(e);
					}
				}
			}
		};
		LogFactory.getDefault().addLogListener(fErrorLogListener);
	}
	
	public CoreReleaseTests() {
		addTest(ArgFileContentAssistTests.suite());
		addTest(ArgFileIndex2Tests.suite());
		addTest(new TestSuite(TestArgFileCreator.class));
		addTest(ArgFileOpenDeclTests.suite());
		addTest(ArgFileParserTests.suite());
		addTest(new TestSuite(SVScannerTests.class));
		addTest(ParserTests.suite());
		addTest(ParserAMSTests.suite());
		addTest(ParserDBTests.suite());
		addTest(new TestSuite(PreProcMacroTests.class));
		addTest(PreProcTests.suite());
		addTest(IndentTests.suite());
		addTest(IndexRefTests.suite());
		addTest(JobMgrTests.suite());
		addTest(ContentAssistTests.suite());
		addTest(PersistenceTests.suite());
		addTest(ProjectSettingsTests.suite());
		addTest(IndexTests.suite());
		addTest(IndexCacheTests.suite());
		addTest(SrcGenTests.suite());
		addTest(LogScannerTests.suite());
		addTest(OpenDeclTests.suite());
		addTest(PrimitivesTests.suite());
		addTest(new TestSuite(FileSetTests.class));
		addTest(SearchUtilsTests.suite());
		addTest(SVDBTests.suite());
//		addTest(SearchTests.suite());
		addTest(HierarchyTests.suite());
		addTest(DocsTests.suite());
		
	}
	
	public static List<Exception> getErrors() {
		return fErrors;
	}
	
	public static void clearErrors() {
		fErrors.clear();
	}
	
	
	@Override
	public void run(TestResult result) {
		SVCorePlugin.getDefault().enableDebug(false);
		// TODO Auto-generated method stub
		super.run(result);
	}
	
	@Override
	public void runTest(Test test, TestResult result) {
		SVCorePlugin.getDefault().enableDebug(false);
		super.runTest(test, result);
	}



	public static Test suite() {
		
		/*
		TestSuite suite = new TestSuite();
		suite.addTest(new TestSuite(SVScannerTests.class));
		suite.addTest(IndentTests.suite());
		suite.addTest(ContentAssistTests.suite());
		suite.addTest(PersistenceTests.suite());
		suite.addTest(IndexTests.suite());
		
		return suite;
		 */
		return new CoreReleaseTests();
	}
	
}
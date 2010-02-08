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


package net.sf.sveditor.core.tests.content_assist;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;
import junit.framework.TestCase;

public class ContentAssistBasics extends TestCase {
	private SVDBIndexCollectionMgr		fIndexCollectionMgr;
	private File						fTmpDir;
	
	@Override
	public void setUp() {
		fTmpDir = TestUtils.createTempDir();
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/data/basic_content_assist_project", fTmpDir);

		String pname = "basic_content_assist_project";
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		fIndexCollectionMgr = new SVDBIndexCollectionMgr(pname);
		fIndexCollectionMgr.addPluginLibrary(
				rgy.findCreateIndex(pname, "net.sf.sveditor.ovm_2.0.1", 
						SVDBPluginLibIndexFactory.TYPE, null));
				
	}
	
	public void testUntriggeredClassAssist() {
		String doc1 = 
			"class my_class;\n" +
			"    <<FIELD1>>\n" +
			"    m_data <<FIELD2>>\n" +
			"endclass\n";
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		SVDBFileFactory factory = new SVDBFileFactory();
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

		TestCompletionProcessor cp = new TestCompletionProcessor(file, fIndexCollectionMgr);
		
		scanner.seek(tt_utils.getPosMap().get("FIELD1"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("FIELD1"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			System.out.println("proposal: " + p.getReplacement());
		}
		
		
		String doc2 = 
			"class my_class;\n" +
			"    ovm_c<<FIELD1>>\n" +
			"endclass\n";
		
	}
	
	public void testNonPrefixInclude() {
		
	}
	
	public void testPrefixInclude() {
		
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		// fTmpDir.delete();
	}

}

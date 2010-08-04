package net.sf.sveditor.core.tests.content_assist;

import java.io.File;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBIndexValidator;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestContentAssistBuiltins extends TestCase {
	private ContentAssistIndex			fIndex;
	private SVDBIndexCollectionMgr		fIndexMgr;
	private File						fTmpDir;
	
	@Override
	public void setUp() {
		fTmpDir = TestUtils.createTempDir();
		
		fIndexMgr = new SVDBIndexCollectionMgr("TestContentAssistBuiltins");
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		fIndexMgr.addPluginLibrary(
				rgy.findCreateIndex("TestContentAssistBuiltins", 
						SVCorePlugin.SV_BUILTIN_LIBRARY, 
						SVDBPluginLibIndexFactory.TYPE, null));

		fIndex = new ContentAssistIndex();
		fIndexMgr.addLibraryPath(fIndex);
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		fTmpDir.delete();
	}

	public void testCovergroupOption() {
		String doc =
			"class my_class1;\n" +							// 1
			"\n" +
			"    covergroup foo;\n" +
			"        option.per_<<MARK>>\n" +
			"    endgroup\n" +
			"endclass\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		ISVDBItemIterator<SVDBItem> it = index_it.getItemIterator();
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it.getItemIterator(), SVDBIndexValidator.ExpectErrors);
		
		SVDBCoverGroup cg = null;
		SVDBModIfcClassDecl my_class1 = null;
		it = index_it.getItemIterator();
		
		while (it.hasNext()) {
			SVDBItem it_t = it.nextItem();
			
			if (it_t.getType() == SVDBItemType.Covergroup && 
					it_t.getName().equals("foo")) {
				cg = (SVDBCoverGroup)it_t;
			} else if (it_t.getType() == SVDBItemType.Class &&
					it_t.getName().equals("my_class1")) {
				my_class1 = (SVDBModIfcClassDecl)it_t;
			}
		}
		
		assertNotNull(cg);
		assertNotNull(my_class1);
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"per_instance"}, proposals);
	}

	public void testCovergroupTypeOptionMergeInstances() {
		String doc =
			"class my_class1;\n" +							// 1
			"\n" +
			"    covergroup foo;\n" +
			"        type_option.mer<<MARK>>\n" +
			"    endgroup\n" +
			"endclass\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		ISVDBItemIterator<SVDBItem> it = index_it.getItemIterator();
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it.getItemIterator(), SVDBIndexValidator.ExpectErrors);
		
		SVDBCoverGroup cg = null;
		SVDBModIfcClassDecl my_class1 = null;
		it = index_it.getItemIterator();
		
		while (it.hasNext()) {
			SVDBItem it_t = it.nextItem();
			
			if (it_t.getType() == SVDBItemType.Covergroup && 
					it_t.getName().equals("foo")) {
				cg = (SVDBCoverGroup)it_t;
			} else if (it_t.getType() == SVDBItemType.Class &&
					it_t.getName().equals("my_class1")) {
				my_class1 = (SVDBModIfcClassDecl)it_t;
			}
		}
		
		assertNotNull(cg);
		assertNotNull(my_class1);
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		assertEquals(1, proposals.size());
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"merge_instances"}, proposals);
	}

	/*************** Utility Methods ********************/
	private Tuple<SVDBFile, TextTagPosUtils> contentAssistSetup(String doc) {
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.getDefault().createFileFactory(null);
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc");
		fIndex.setFile(file);

		return new Tuple<SVDBFile, TextTagPosUtils>(file, tt_utils);
	}
	
	private void validateResults(String expected[], List<SVCompletionProposal> proposals) {
		for (String exp : expected) {
			boolean found = false;
			for (int i=0; i<proposals.size(); i++) {
				if (proposals.get(i).getReplacement().equals(exp)) {
					found = true;
					proposals.remove(i);
					break;
				}
			}
			
			assertTrue("Failed to find content proposal " + exp, found);
		}
		
		for (SVCompletionProposal p : proposals) {
			System.out.println("[ERROR] Unexpected proposal " + p.getReplacement());
		}
		assertEquals("Unexpected proposals", 0, proposals.size());
	}

}

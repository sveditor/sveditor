package net.sf.sveditor.core.tests.argfile.content_assist;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.TextTagPosUtils;
import net.sf.sveditor.core.tests.content_assist.TestCompletionProcessor;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestArgFilePathContentAssist extends SVCoreTestCaseBase {

	public void tbd_testFilePathContentAssist() {
		String doc =
			"${workspace_loc}/foo.sv\n" +
			"${workspace_loc}/" + getName() + "/<<MARK>>\n"
			;
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		IProject p = TestUtils.createProject(getName());
		addProject(p);
		
		TestUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				p.getFile("cls1.svh"));
		
		TestUtils.copy(
				"class cls2;\n" +
				"endclass\n",
				p.getFile("cls2.svh"));
		
		TestUtils.mkdir(p, "subdir");
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), getName(), markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			fLog.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestArgFileCompletionProcessor cp = new TestArgFileCompletionProcessor(fLog);
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

//		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));		
	}

}

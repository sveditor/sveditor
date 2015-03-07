package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestTaskTags extends SVCoreTestCaseBase {
	
	public void testColonTags() {
		String doc =
			"module top;\n" +
			"	// TODO: must fix this implementation\n" +
			"	always @(posedge clk) begin\n" +
			"	end\n" +
			"endmodule\n"
			;
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBTestUtils.parse(fLog, doc, getName(), markers);
	
		assertEquals(1, markers.size());
		assertEquals(SVDBMarker.MarkerType.Task, markers.get(0).getMarkerType());
		assertEquals("TODO: must fix this implementation",
				markers.get(0).getMessage());
	}

	public void testNoColonTags() {
		String doc =
			"module top;\n" +
			"	// TODO must fix this implementation\n" +
			"	always @(posedge clk) begin\n" +
			"	end\n" +
			"endmodule\n"
			;
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBTestUtils.parse(fLog, doc, getName(), markers);
	
		assertEquals(1, markers.size());
		assertEquals(SVDBMarker.MarkerType.Task, markers.get(0).getMarkerType());
		assertEquals("TODO must fix this implementation",
				markers.get(0).getMessage());
	}
	
	public void testIgnoreNonTaskTags() {
		String doc =
			"module top;\n" +
			"	// FOOBAR must fix this implementation\n" +
			"	always @(posedge clk) begin\n" +
			"	end\n" +
			"endmodule\n"
			;
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBTestUtils.parse(fLog, doc, getName(), markers);
	
		assertEquals(0, markers.size());
	}
	
}

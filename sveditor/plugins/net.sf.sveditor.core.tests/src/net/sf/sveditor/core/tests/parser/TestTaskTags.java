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

	public void testTaskInMLCOne() {
		String doc =
				"module top;\n" +
						"	/* TODO: must fix this implementation*/\n" +
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
	
	public void testTaskInMLC() {
		String doc =
				"module top;\n" +
						"	/*\n" +
						"	 * FIXME must fix this implementation\n" +
						"	 */\n" +
						"	always @(posedge clk) begin\n" +
						"	end\n" +
						"endmodule\n"
						;
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBTestUtils.parse(fLog, doc, getName(), markers);
		
		assertEquals(1, markers.size());
		assertEquals(SVDBMarker.MarkerType.Task, markers.get(0).getMarkerType());
		assertEquals("FIXME must fix this implementation",
				markers.get(0).getMessage());
	}
	
	public void testTaskNoReason() {
		String doc =
				"module top;\n" +
						"	/**\n" +
						"	 * FIXME\n" +
						"	 */\n" +
						"	always @(posedge clk) begin end\n" +
						"	/**\n" +
						"	 * FIXME:\n" +
						"	 */\n" +
						"	always @(posedge clk) begin end\n" +
						"	/**\n" +
						"	 * FIXME: \n" +
						"	 */\n" +
						"	always @(posedge clk) begin end\n" +
						"	/**\n" +
						"	 * FIXME: thing\n" +
						"	 */\n" +
						"	always @(posedge clk) begin\n" +
						"	end\n" +
						"endmodule\n"
						;
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBTestUtils.parse(fLog, doc, getName(), markers);
		String S;
		for (int i=0; i<markers.size(); i++)  {
			S = markers.get(i).getMessage();
		}
		assertEquals(4, markers.size());
		assertEquals(SVDBMarker.MarkerType.Task, markers.get(0).getMarkerType());
		assertEquals("FIXME ", markers.get(0).getMessage());
		assertEquals(SVDBMarker.MarkerType.Task, markers.get(1).getMarkerType());
		assertEquals("FIXME :", markers.get(1).getMessage());
		assertEquals(SVDBMarker.MarkerType.Task, markers.get(2).getMarkerType());
		assertEquals("FIXME: ", markers.get(2).getMessage());
		assertEquals(SVDBMarker.MarkerType.Task, markers.get(3).getMarkerType());
		assertEquals("FIXME: thing", markers.get(3).getMessage());
	}
	

}

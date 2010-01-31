package net.sf.sveditor.core.db;

public class SVDBItemPrint {
	
	public static void printItem(SVDBItem item) {
		printItem(0, item);
	}
	
	private static void printItem(int indent, SVDBItem item) {
		for (int i=0; i<indent; i++) {
			System.out.print(" ");
		}
		
		System.out.print("" + item.getType() + " " + item.getName());
		
		if (item instanceof SVDBPreProcCond) {
			System.out.print(" " + ((SVDBPreProcCond)item).getConditional());
		}
		System.out.println();
		
		if (item instanceof SVDBScopeItem) {
			for (SVDBItem it : ((SVDBScopeItem)item).getItems()) {
				printItem(indent+4, it);
			}
		}
	}

}

package net.sf.sveditor.core;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

public class SortUtils {
	
	public static List<String> sortStringList(List<String> l, boolean ascending) {
		List<String> ret = new ArrayList<String>();
		ret.addAll(l);
		
		
		
		return ret;
	}
	
	@SuppressWarnings({"rawtypes","unchecked"})
	public static void sort(List l, Comparator c, boolean ascending) {
		for (int i=0; i<l.size(); i++) {
			for (int j=i+1; j<l.size(); j++) {
				Object o_i = l.get(i);
				Object o_j = l.get(j);
				
				int r;
				if ((r = c.compare(o_i, o_j)) != 0) {
					if (r > 0 && ascending) {
						l.set(i, o_j);
						l.set(j, o_i);
					}
				}
			}
		}
	}

}

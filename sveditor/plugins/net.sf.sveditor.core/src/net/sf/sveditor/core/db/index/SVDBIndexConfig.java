package net.sf.sveditor.core.db.index;

import java.util.HashMap;
import java.util.Map;

public class SVDBIndexConfig extends HashMap<String, Object> {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	
	public static boolean equals(SVDBIndexConfig c1, SVDBIndexConfig c2) {
		if (c1 == null || c2 == null) {
			return (c1 == c2);
		} else {
			boolean equals = c1.size() == c2.size();
			
			if (equals) {
				// Compare attributes
				for (Map.Entry<String, Object> c1_e : c1.entrySet()) {
					if (c2.containsKey(c1_e.getKey())) {
						Object o1 = c1.get(c1_e.getKey());
						Object o2 = c2.get(c1_e.getKey());
						
						if (o1 == null || o2 == null) {
							equals &= (o1 == o2);
						} else {
							equals &= o1.equals(o2);
						}
					} else { 
						equals = false;
					}
					
					if (!equals) {
						break;
					}
				}
			}
			
			return equals;
		}
	}

}

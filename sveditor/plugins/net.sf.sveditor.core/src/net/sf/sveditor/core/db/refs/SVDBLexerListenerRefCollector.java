/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.parser.ISVTokenListener;
import net.sf.sveditor.core.parser.SVToken;

public class SVDBLexerListenerRefCollector implements ISVTokenListener {
	
	private Map<String, List<Integer>>			fRefMap;
	private Map<String, long[]>					fRefMapS;
	
	public SVDBLexerListenerRefCollector() {
		fRefMap = new HashMap<String, List<Integer>>();
		fRefMapS = new HashMap<String, long[]>();
	}
	
	public Map<String, List<Integer>> getRefMap() {
		Map<String, List<Integer>> ret = new HashMap<String, List<Integer>>();
		long start = System.currentTimeMillis();
		for (Entry<String, long[]> ent : fRefMapS.entrySet()) {
			String id = ent.getKey();
			long files[] = ent.getValue();
			
			List<Integer> file_list = new ArrayList<Integer>();
			for (int i=0; i<files.length; i++) {
				if (files[i] != 0) {
					for (int j=0; j<64; j++) {
						if ((files[i] & (1 << j)) != 0) {
							file_list.add(64*i+j);
						}
					}
				}
			}
			ret.put(id, file_list);
		}
		long end = System.currentTimeMillis();
		
		System.out.println("demap: " + (end-start));
		
		return ret;
	}

	@Override
	public void tokenConsumed(SVToken tok) {
		if (tok.isIdentifier()) {
			int file_id = SVDBLocation.unpackFileId(tok.getStartLocation());
			String name = tok.getImage();
			long file_list[] = fRefMapS.get(name);
			
			int n_elem = ((file_id/64)+1);
			if (file_list == null || file_list.length < n_elem) {
				long new_file_list[] = new long[(((n_elem-1)/4)+1)*4];
				if (file_list != null) {
					System.arraycopy(new_file_list, 0, file_list, 0, file_list.length);
					fRefMapS.remove(name);
				}
				fRefMapS.put(name, new_file_list);
				file_list = new_file_list;
			}
		
			file_list[file_id/64] |= (1 << (file_id&63));
		}
	}

	@Override
	public void ungetToken(SVToken tok) { }

}

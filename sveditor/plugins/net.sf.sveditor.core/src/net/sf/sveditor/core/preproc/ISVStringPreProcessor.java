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
package net.sf.sveditor.core.preproc;

import java.io.InputStream;

public interface ISVStringPreProcessor {
	
	void addListener(IPreProcListener l);
	
	void removeListener(IPreProcListener l);

	/**
	 * Specifies whether `line directives should be emitted
	 * 
	 * @param emit
	 */
	void setEmitLineDirectives(boolean emit);
	
	String preprocess(InputStream in);

}

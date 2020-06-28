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
package net.sf.sveditor.core.checker;

import net.sf.sveditor.core.db.ISVDBItemBase;

public interface ISVDBCheckVisitor {
	
	void visit(
			ISVDBCheckErrorReporter		err_reporter,
			ISVDBItemBase 				it);

}

/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package org.sveditor.core.docs;

import java.io.File;

import org.sveditor.core.docs.model.DocModel;

public interface IDocWriter {
	
	public void write(DocGenConfig cfg, DocModel model) ;
	
	public File getIndexHTML(DocGenConfig cfg, DocModel model) ;

}

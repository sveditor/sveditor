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
package org.sveditor.ui.editor;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModelFactory;

public class SVEditorAnnotationModelFactory extends ResourceMarkerAnnotationModelFactory {

	public IAnnotationModel createAnnotationModel(IPath location) {
		
		IFile file= FileBuffers.getWorkspaceFileAtLocation(location);
		if (file != null) {
			
		}
		
		return super.createAnnotationModel(location);
	}

}

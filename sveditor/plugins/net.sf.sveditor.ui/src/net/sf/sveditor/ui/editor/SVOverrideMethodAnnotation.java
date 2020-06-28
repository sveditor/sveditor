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
package net.sf.sveditor.ui.editor;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.jface.text.source.Annotation;

public class SVOverrideMethodAnnotation extends Annotation {
	private SVDBTask			fTF;
	
	public SVOverrideMethodAnnotation(SVDBTask tf, String msg) {
		super(SVUiPlugin.PLUGIN_ID + ".methodOverride", false, msg);
		fTF = tf;
	}

	public SVDBTask getTask() {
		return fTF;
	}
}

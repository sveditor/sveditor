/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Steven Dawson - initial implementation
 ****************************************************************************/

package org.eclipse.hdt.sveditor.ui.explorer;

import java.io.InputStream;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.indent.ISVIndenter;
import org.eclipse.hdt.sveditor.core.indent.SVIndentScanner;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;

public class IndentHandler extends AbstractHandler implements IHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		ISelection sel = HandlerUtil.getCurrentSelection(event);

		if (sel instanceof IStructuredSelection) {
			IStructuredSelection sel_s = (IStructuredSelection) sel;

			IFile file = null;
			for (Object s : sel_s.toArray()) {

				if (s instanceof IFile) {
					file = (IFile) s;
				} else if (s instanceof IAdaptable) {
					file = (IFile) ((IAdaptable) s).getAdapter(IFile.class);
				}

				if (file == null) {
					break;
				}
				try {
					InputStream is = file.getContents();
					StringBuilder sb = new StringBuilder();
					int ch;
					do {
						ch = is.read();
						if (ch != -1) {
							sb.append((char) ch);
						}
					} while (ch != -1);
					String contents = sb.toString();
					SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(contents));
					ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
					indenter.init(scanner);

					String result = indenter.indent(-1, -1);
					InputStream in_s = new StringInputStream(result);
					file.setContents(in_s, true, false, new NullProgressMonitor());

				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}

		return null;
	}

}

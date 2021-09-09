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

package org.sveditor.ui.explorer;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.StringInputStream;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.index.SVDBIndexUtil;
import org.sveditor.core.docs.DocCommentAdder;
import org.sveditor.core.docs.IDocCommentAdder;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;

public class AddNdocsHandler extends AbstractHandler implements IHandler {

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
					continue;
				}
				try {
					// For better or worse... right now we are getting what is on the disk, not what is in the editor
					// TODO: Check if the editor is open and dirty.  If so, prompt for a save, and allow DB to rebuild before
					//       continuing
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

					// Get the SVDB for this file
					SVDBFile svdbf = SVDBIndexUtil.findIndexFile(file);

					IDocCommentAdder dca = new DocCommentAdder(svdbf, SVDBIndexUtil.findIndexIterator(file), true);
					ArrayList<Tuple<Object, String>> fComments = dca.AddComments(-1);
					ArrayList<String> lines = new ArrayList<String>(Arrays.asList(contents.split("\n")));
					// Restore \n's
					for (int i=0; i<lines.size(); i++)  {
						lines.set(i, lines.get(i) + "\n");
					}

					// Insert the comments as appropriate
					// Start at the last comment to be inserted and work backwards as this will change subsequent line numbers
					while (fComments.size() > 0)  {
						int highest_comment = -1;
						int highest_index = -1;
						String highest_string = "";

						// Find the comment closest to the end of the file
						for (int i=0; i<fComments.size(); i++)  {
							Integer offset = (Integer)fComments.get(i).first();
							if (offset > highest_comment)  {
								// Get comment and line number
								highest_comment = offset;
								highest_string = fComments.get(i).second();
								highest_index = i;
							}
						}
						
						// Check if we have a mismatch between what we currently have in the editor and what 
						// we had on our last compile... if things don't match 
						if (highest_comment > lines.size())  {
							// TODO: The file has shrunk for some reason... need to re-compile here
							break;
						}
						if (highest_string != "")  {
							// Figure out leading whitespace where we are going to insert comment
							String leadingWS = lines.get(highest_comment-1);
							leadingWS = leadingWS.replaceAll("[a-zA-Z0-9_].*", "");
							leadingWS = leadingWS.replaceAll("\n", "");
							highest_string = leadingWS + highest_string.replaceAll("\n",  "\n" + leadingWS);
							highest_string = highest_string.substring(0, highest_string.length()-leadingWS.length());	// Remove trailing whitespace
							lines.add(highest_comment-1, highest_string);
						}
						fComments.remove(highest_index);
						
					}
					
					sb.setLength(0);
					for (String line : lines)  {
						sb.append(line);
					}
					InputStream in_s = new StringInputStream(sb.toString());
					file.setContents(in_s, true, false, new NullProgressMonitor());

				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}

		return null;
	}

}

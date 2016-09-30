/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Steven Dawson - initial implementation
 ****************************************************************************/

package net.sf.sveditor.ui.explorer;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.docs.DocCommentAdder;
import net.sf.sveditor.core.docs.IDocCommentAdder;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.parser.SVParserConfig;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.NullProgressMonitor;
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
					Tuple<ISVDBIndex, SVDBIndexCollection> result;
					String project_name = file.getProject().getName();
					String file_path = file.getFullPath().toString();
					file_path = "${workspace_loc}" + file_path;
					result = SVDBIndexUtil.findIndexFile(file_path, project_name, false);
					if (result == null)  {
						continue;
					}
					SVDBFile svdbf = result.first().findFile(file_path);

					StringTextScanner scanner = new StringTextScanner(contents);
					IDocCommentAdder dca = new DocCommentAdder(svdbf, scanner, true);
					ArrayList<Tuple<Object, String>> fComments = dca.addcomments(-1);
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
							if ((int) fComments.get(i).first() > highest_comment)  {
								// Get comment and line number
								highest_comment = (int) fComments.get(i).first();
								highest_string = fComments.get(i).second();
								highest_index = i;
							}
						}
						
						if (highest_string != "")  {
							lines.add(highest_comment-1, highest_string);
						}
						fComments.remove(highest_index);
						
					}
					
					String output;
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

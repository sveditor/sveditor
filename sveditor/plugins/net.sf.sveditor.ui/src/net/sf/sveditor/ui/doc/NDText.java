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
package net.sf.sveditor.ui.doc;

import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.html.HTMLFromNDMarkup;
import net.sf.sveditor.core.docs.model.DocTopic;

import org.eclipse.jface.text.TextPresentation;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.widgets.Composite;

/**
 * Text widget that formats NaturalDocs content
 * 
 * @author ballance
 *
 */
public class NDText extends StyledText {
	
	public NDText(Composite parent, int style) {
		super(parent, style);
	}

	@Override
	public void setText(String text) {
		

		if (!text.equals("")) {
			String temp = "general: abc\n" + text;
			DocTopicManager topic_mgr = new DocTopicManager();
			DocCommentParser parser = new DocCommentParser(topic_mgr);
			List<DocTopic> topics = new ArrayList<DocTopic>();
			parser.parse(temp, topics);
			
			if (topics.size() > 0) {
				HTMLFromNDMarkup markupConverter = new HTMLFromNDMarkup() ;
				text = markupConverter.convertNDMarkupToHTML(null, topics.get(0), 
						topics.get(0).getBody(), HTMLFromNDMarkup.NDMarkupToHTMLStyle.Tooltip);
			} 
		}

		TextPresentation presentation = new TextPresentation(getSize().x);
		HTML2TextReader rdr = new HTML2TextReader(
				new StringReader(text), presentation);

		try {
			super.setText(rdr.getString());
			rdr.close();
		} catch (IOException e) {}
		TextPresentation.applyTextPresentation(presentation, this);
	}

}

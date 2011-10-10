/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.templates.ContextTypeRegistry;
import org.eclipse.jface.text.templates.Template;
import org.eclipse.jface.text.templates.TemplateCompletionProcessor;
import org.eclipse.jface.text.templates.TemplateContext;
import org.eclipse.jface.text.templates.TemplateContextType;
import org.eclipse.jface.text.templates.TemplateException;
import org.eclipse.swt.graphics.Image;

public class SVTemplateCompletionProcessor extends TemplateCompletionProcessor {
	private SVEditor							fEditor;
	private SVCompletionProcessor				fSubProcessor;

	@SuppressWarnings("rawtypes")
	private static final class ProposalComparator implements Comparator {
		public int compare(Object o1, Object o2) {
			return ((SVIndentingTemplateProposal) o2).getRelevance() - ((SVIndentingTemplateProposal) o1).getRelevance();
		}
	}
	@SuppressWarnings("rawtypes")
	private static final Comparator fgProposalComparator= new ProposalComparator();
	

	public SVTemplateCompletionProcessor(SVEditor editor) {
		fEditor = editor;
		fSubProcessor = new SVCompletionProcessor(fEditor);
	}

	@Override
	public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer,
			int offset) {
		List<ICompletionProposal> proposals = new ArrayList<ICompletionProposal>();

		for (ICompletionProposal p : computeTemplateCompletionProposals(viewer, offset)) {
			proposals.add(p);
		}
		
		for (ICompletionProposal p : fSubProcessor.computeCompletionProposals(viewer, offset)) {
			proposals.add(p);
		}
		
		return proposals.toArray(new ICompletionProposal[proposals.size()]);
	}
	
	@SuppressWarnings("unchecked")
	private ICompletionProposal[] computeTemplateCompletionProposals(ITextViewer viewer, int offset) {

		ITextSelection selection= (ITextSelection) viewer.getSelectionProvider().getSelection();

		// adjust offset to end of normalized selection
		if (selection.getOffset() == offset)
			offset= selection.getOffset() + selection.getLength();

		String prefix= extractPrefix(viewer, offset);
		Region region= new Region(offset - prefix.length(), prefix.length());
		TemplateContext context= createContext(viewer, region);
		if (context == null)
			return new ICompletionProposal[0];

		context.setVariable("selection", selection.getText()); // name of the selection variables {line, word}_selection //$NON-NLS-1$

		Template[] templates= getTemplates(context.getContextType().getId());

		List<Object> matches = new ArrayList<Object>();
		for (int i= 0; i < templates.length; i++) {
			Template template= templates[i];
			try {
				context.getContextType().validate(template.getPattern());
			} catch (TemplateException e) {
				continue;
			}
			
			if (context.getContextType().getId().equals(template.getContextTypeId()) &&
					template.getPattern().toLowerCase().startsWith(prefix.toLowerCase())) {
				matches.add(createProposal(template, context, (IRegion) region, getRelevance(template, prefix)));
			}
		}

		Collections.sort(matches, fgProposalComparator);

		return (ICompletionProposal[]) matches.toArray(new ICompletionProposal[matches.size()]);
	}

	
	@Override
	protected ICompletionProposal createProposal(Template template,
			TemplateContext context, IRegion region, int relevance) {
		return new SVIndentingTemplateProposal(
				template, context, region, getImage(template), relevance);
	}

	@Override
	protected TemplateContextType getContextType(
			ITextViewer 		viewer,
			IRegion 			region) {
		ContextTypeRegistry rgy = SVUiPlugin.getDefault().getContextTypeRegistry();
		return rgy.getContextType(SVUiPlugin.SV_TEMPLATE_CONTEXT);
	}

	@Override
	protected Image getImage(Template template) {
		ImageRegistry rgy = SVUiPlugin.getDefault().getImageRegistry();
		
        return rgy.get("icons/template.gif");
	}

	public Template[] getTemplates(String contextId) {
		return SVUiPlugin.getDefault().getTemplateStore().getTemplates();
	}

}

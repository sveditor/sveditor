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
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.contentassist.ContentAssistEvent;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.ICompletionListener;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistantExtension2;
import org.eclipse.jface.text.templates.ContextTypeRegistry;
import org.eclipse.jface.text.templates.Template;
import org.eclipse.jface.text.templates.TemplateCompletionProcessor;
import org.eclipse.jface.text.templates.TemplateContext;
import org.eclipse.jface.text.templates.TemplateContextType;
import org.eclipse.swt.graphics.Image;

public class SVTemplateCompletionProcessor extends TemplateCompletionProcessor 
		implements ICompletionListener {
	private enum CompletionState {
		AllContext,
		JustTemplates
	}
	
	private CompletionState						fState;
	private SVEditor							fEditor;
	private SVEditorCompletionProcessor				fSubProcessor;
	private IContentAssistantExtension2			fAssistant;

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
		fSubProcessor = new SVEditorCompletionProcessor(fEditor);
	}

	@Override
	@SuppressWarnings("unchecked")
	public ICompletionProposal[] computeCompletionProposals(
			ITextViewer 	viewer,
			int 			offset) {
		ITextSelection selection= (ITextSelection) viewer.getSelectionProvider().getSelection();

		// adjust offset to end of normalized selection
		if (selection.getOffset() == offset) {
			offset= selection.getOffset() + selection.getLength();
		}

		String prefix = extractPrefix(viewer, offset);
		Region region = new Region(offset - prefix.length(), prefix.length());
		TemplateContext context = createContext(viewer, region);
		
		if (context != null) {
			context.setVariable("selection", selection.getText()); // name of the selection variables {line, word}_selection //$NON-NLS-1$
		}
		
		List<ICompletionProposal> proposals = new ArrayList<ICompletionProposal>();
		IBIDITextScanner scanner = SVEditorCompletionProcessor.createScanner(viewer, offset);
		Tuple<Integer, Integer> line_pos = SVEditorCompletionProcessor.computeLineOffset(viewer, offset);
		
		if (line_pos == null) {
			return new ICompletionProposal[0];
		}
	
		SVExprContext ctxt = fSubProcessor.computeExprContext(scanner, line_pos.first());
	
		if (fState == CompletionState.AllContext) {
			List<ICompletionProposal> template_proposals = new ArrayList<ICompletionProposal>();
			List<ICompletionProposal> template_proposals_id = new ArrayList<ICompletionProposal>();
			List<Template> template_l = null;
			// In the AllContext state, we add templates if the context is a
			// non-triggered context
		
			if (context != null && ctxt.fTrigger == null) {
				template_l = getTemplates(context);

				addTemplatesByPattern(template_proposals, context, region, template_l, prefix);
				Collections.sort(template_proposals, fgProposalComparator);
				proposals.addAll(template_proposals);
				addTemplatesById(template_proposals_id, context, region, template_l, prefix);
			}
			
			fSubProcessor.calculateCompletionProposals(proposals, viewer, offset);
			
			if (template_proposals_id.size() > 0) {
				// There are ID-selected templates to show
				fAssistant.setStatusLineVisible(true);
				fAssistant.setStatusMessage("Press 'Ctrl+Space' to see Template Proposals");
				fState = CompletionState.JustTemplates;
		
				// Could be more proposals
				ContentAssistant a = (ContentAssistant)fAssistant;
				a.enablePrefixCompletion(false);
			} else {
				((ContentAssistant)fAssistant).enablePrefixCompletion(true);
			}
		} else if (fState == CompletionState.JustTemplates) {
			List<Template> template_l = null;
			List<ICompletionProposal> template_proposals_id = new ArrayList<ICompletionProposal>();
			
			if (context != null) {
				template_l = getTemplates(context);
				addTemplatesById(template_proposals_id, context, region, template_l, prefix);
				Collections.sort(template_proposals_id, fgProposalComparator);
				proposals.addAll(template_proposals_id);
			}
			
			fAssistant.setStatusLineVisible(true);
			fAssistant.setStatusMessage("Press 'Ctrl+Space' to see Default Proposals");
			fState = CompletionState.AllContext;
		}
		
		
		return proposals.toArray(new ICompletionProposal[proposals.size()]);
	}
	
	private void addTemplatesByPattern(
			List<ICompletionProposal>	template_proposals,
			TemplateContext				context,
			IRegion						region,
			List<Template>				templates,
			String						prefix) {
		for (int i=0; i<templates.size(); i++) {
			Template t = templates.get(i);
			if (t.getPattern().toLowerCase().startsWith(prefix.toLowerCase())) {
				ICompletionProposal p;
				p = createProposal(t, context, region, getRelevance(t, prefix));
				template_proposals.add(p);
			}
		}
	}
	
	private void addTemplatesById(
			List<ICompletionProposal>		template_proposals,
			TemplateContext					context,
			IRegion							region,
			List<Template>					templates,
			String							prefix) {
		for (int i=0; i<templates.size(); i++) {
			Template t = templates.get(i);

//			System.out.println("name=" + t.getName() + " prefix=" + prefix);
			if (t.getName().toLowerCase().startsWith(prefix.toLowerCase())) {
				ICompletionProposal p;
//				System.out.println("  ADD");
				p = createProposal(t, context, region, getRelevance(t, prefix));
				template_proposals.add(p);
			}
		}
		
	}

	/** Old code
	@SuppressWarnings("unchecked")
	private ICompletionProposal[] computeTemplateCompletionProposals(
			ITextViewer viewer, 
			int 		offset,
			boolean		filter) {

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
		
//			System.out.println("context=" + context.getContextType().getId() + " template.context=" + template.getContextTypeId());
			if (!filter || (context.getContextType().getId().equals(template.getContextTypeId()) &&
							!prefix.trim().equals("") && 
							template.getPattern().toLowerCase().startsWith(prefix.toLowerCase()))) {
				matches.add(createProposal(template, context, (IRegion) region, getRelevance(template, prefix)));
			}
		}

		Collections.sort(matches, fgProposalComparator);

		return (ICompletionProposal[]) matches.toArray(new ICompletionProposal[matches.size()]);
	}
	 */

	/**
	 * Get all 
	 * @param viewer
	 * @param offset
	 * @return
	 */
	private List<Template> getTemplates(TemplateContext context) {
		List<Template> template_l = new ArrayList<Template>();

		if (context != null) {
			Template[] templates= getTemplates(context.getContextType().getId());

			for (Template t : templates) {
				if (context.getContextType().getId().equals(t.getContextTypeId())) {
					template_l.add(t);
				}
			}
		}

		return template_l;
	}

	
	@Override
	public void assistSessionStarted(ContentAssistEvent event) {
		fAssistant = (IContentAssistantExtension2)event.assistant;
		fAssistant.setStatusLineVisible(false);
		fState = CompletionState.AllContext;
		((ContentAssistant)fAssistant).enablePrefixCompletion(false);
	}

	@Override
	public void assistSessionEnded(ContentAssistEvent event) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void selectionChanged(ICompletionProposal proposal,
			boolean smartToggle) {
		// TODO Auto-generated method stub
		
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

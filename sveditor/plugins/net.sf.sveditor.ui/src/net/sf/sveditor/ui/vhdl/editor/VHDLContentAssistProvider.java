package net.sf.sveditor.ui.vhdl.editor;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.jface.text.templates.DocumentTemplateContext;
import org.eclipse.jface.text.templates.Template;
import org.eclipse.jface.text.templates.TemplateContext;
import org.eclipse.jface.text.templates.TemplateContextType;
import org.eclipse.jface.text.templates.TemplateProposal;

public class VHDLContentAssistProvider implements IContentAssistProcessor {
	private List<VHDLProposalInfo>					fTemplateList;
	
	public VHDLContentAssistProvider() {
		IExtensionRegistry rgy = Platform.getExtensionRegistry();

		fTemplateList = new ArrayList<VHDLProposalInfo>();

		// TODO: add VHDL template-based content assist
//		IExtensionPoint ept = rgy.getExtensionPoint(
//				VhdlUiPlugin.PLUGIN_ID, "contentAssistTemplates");
//
//		if (ept != null) {
//		for (IExtension ext : ept.getExtensions()) {
//			for (IConfigurationElement ex : ext.getConfigurationElements()) {
//				String trigger = ex.getAttribute("trigger");
////				System.out.println("trigger=" + trigger);
//
//				IConfigurationElement proposal[] = ex.getChildren("proposal");
//				
//				if (proposal != null && proposal.length > 0) {
//					IConfigurationElement template[] = proposal[0].getChildren("template");
//					IConfigurationElement description[] = proposal[0].getChildren("description");
//					
//					if (template != null && template.length != 0 &&
//							description != null && description.length != 0) {
//						fTemplateList.add(new VHDLProposalInfo(
//								trigger, description[0].getValue(), template[0].getValue())); 
//					}
//				}
//			}
//		}
//		}
	}

	public ICompletionProposal[] computeCompletionProposals(
			ITextViewer viewer, int offset) {
		IDocument doc = viewer.getDocument();
		int ch;
		int start = offset;
		int end=-1;
		int replacementOffset, replacementLength;
		String prefix = null;
		List<ICompletionProposal> ret = new ArrayList<ICompletionProposal>();

		try {
			if (start > 0) {
				start--;
				ch = doc.getChar(start);
				if (Character.isJavaIdentifierPart(ch)) {
					end = start;
					while (start > 0 && Character.isJavaIdentifierPart(
							(ch = doc.getChar(start)))) { start--; }
					
					if (start < 0) {
						start = 0;
					} else {
						start++;
					}
					
					if (end > start) {
						prefix = doc.get(start, (end-start)+1);
					}
					
				} else if (Character.isWhitespace(ch)) {
					// See if we can read an entire identifier
					while (start > 0 && Character.isWhitespace(
							(ch = doc.getChar(start)))) { start--; }
					end = start;
					
					if (start > 0) {
						while (start > 0 && Character.isJavaIdentifierPart(
								(ch = doc.getChar(start)))) { start--; }
						if (start < 0) {
							start = 0;
						} else {
							start++;
						}
						if (end > start) {
							prefix = doc.get(start, (end-start)+1);
						}
					}
				}
			}
			
			
		} catch (Exception e) {
			e.printStackTrace();
		}


//		System.out.println("prefix=" + prefix);
		
		if (prefix != null) {
			replacementOffset = start;
			replacementLength = (end-start);

			for (VHDLProposalInfo info : fTemplateList) {
				String trigger = info.fTrigger;
				if (trigger.toLowerCase().startsWith(prefix.toLowerCase())) {
					TemplateContext ctxt = new DocumentTemplateContext(
							new TemplateContextType("CONTEXT"),
							doc, replacementOffset, replacementLength);
					Template t = new Template(info.fDescription, "", "CONTEXT",
							info.fTemplate, true);
					ret.add(new TemplateProposal(
							t, ctxt, new Region(replacementOffset, replacementLength), null));
				}
			}
		}

		return ret.toArray(new ICompletionProposal[ret.size()]);
	}

	public IContextInformation[] computeContextInformation(ITextViewer viewer,
			int offset) {
		// TODO Auto-generated method stub
		return null;
	}

	public char[] getCompletionProposalAutoActivationCharacters() {
		// TODO Auto-generated method stub
		return null;
	}

	public char[] getContextInformationAutoActivationCharacters() {
		// TODO Auto-generated method stub
		return null;
	}

	public IContextInformationValidator getContextInformationValidator() {
		// TODO Auto-generated method stub
		return null;
	}

	public String getErrorMessage() {
		// TODO Auto-generated method stub
		return null;
	}

}

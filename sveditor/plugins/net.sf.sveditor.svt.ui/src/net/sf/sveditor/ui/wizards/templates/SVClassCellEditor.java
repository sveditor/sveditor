package net.sf.sveditor.ui.wizards.templates;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.docs.DocUtil;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprContext.ContextType;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.doc.DocUtilUi;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.jface.bindings.keys.ParseException;
import org.eclipse.jface.fieldassist.ContentProposal;
import org.eclipse.jface.fieldassist.ContentProposalAdapter;
import org.eclipse.jface.fieldassist.IContentProposal;
import org.eclipse.jface.fieldassist.IContentProposalProvider;
import org.eclipse.jface.fieldassist.TextContentAdapter;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.swt.widgets.Composite;

public class SVClassCellEditor extends TextCellEditor implements IContentProposalProvider {
	private IProject fProject;
	
	public SVClassCellEditor(Composite parent) {
		super(parent);
		
		KeyStroke ctrl_space = null;
		try {
			ctrl_space = KeyStroke.getInstance("CTRL+SPACE");
		} catch (ParseException e) { }
	
		ContentProposalAdapter ca = new ContentProposalAdapter(getControl(), new TextContentAdapter(), 
				this, ctrl_space, null);
		ca.setProposalAcceptanceStyle(ContentProposalAdapter.PROPOSAL_REPLACE);
	}
	
	public void setProject(IProject project) {
		fProject = project;
	}

	public IContentProposal[] getProposals(String contents, int position) {
		List<IContentProposal> proposals = new ArrayList<IContentProposal>();
		
		if (fProject != null) {
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBProjectData pdata = pmgr.getProjectData(fProject);
			
			ISVDBIndexIterator index_it = pdata.getProjectIndexMgr();
			
			SVClassCompletionProcessor completionProcessor = new SVClassCompletionProcessor(index_it);
			IBIDITextScanner scanner = new StringBIDITextScanner(contents);
			scanner.seek(position);
			SVExprContext ctxt = new SVExprContext();
			ctxt.fType = ContextType.Extends; // ensure only classes are matched
			ctxt.fLeaf = contents.substring(0, position);
			
			completionProcessor.computeProposals(ctxt, scanner, new SVDBFile(), 1, -1);
			List<SVCompletionProposal> p_l = completionProcessor.getCompletionProposals();
			
			for (SVCompletionProposal p : p_l) {
				// See if there are doc comments associated
				String additional_info = null;
				if (p.getItem() != null) {
					additional_info = DocUtil.getDocComment(index_it, p.getItem());
					
					if (additional_info != null) {
						additional_info = DocUtilUi.formatDoc(additional_info);
					} else {
						additional_info = "";
					}
				}
			
				ContentProposal cp = new ContentProposal(p.getReplacement());
				/*
				CompletionProposal cp = new CompletionProposal(p.getReplacement(), 0, contents.length(),
						p.getReplacement().length(), SVDBIconUtils.getIcon(p.getItem()), 
						"", null, additional_info);
				 */
				proposals.add(cp);
			}
		}
		
		return proposals.toArray(new IContentProposal[proposals.size()]);
	}

}

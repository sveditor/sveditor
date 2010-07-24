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
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.content_assist.SVCompletionProposalType;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.ui.ISVIcons;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.jface.text.templates.DocumentTemplateContext;
import org.eclipse.jface.text.templates.Template;
import org.eclipse.jface.text.templates.TemplateContext;
import org.eclipse.jface.text.templates.TemplateContextType;
import org.eclipse.jface.text.templates.TemplateProposal;


public class SVCompletionProcessor extends AbstractCompletionProcessor 
		implements IContentAssistProcessor {

	private SVEditor 	fEditor;

	private static final char[] PROPOSAL_ACTIVATION_CHARS = { '.', ':' };
	private final IContextInformation NO_CONTEXTS[] = new IContextInformation[0];
	
	private List<ICompletionProposal>				fProposals = 
		new ArrayList<ICompletionProposal>();

	public SVCompletionProcessor(SVEditor editor) {
		fLog = LogFactory.getLogHandle("SVCompletionProcessor");
		fEditor = editor;
	}
	
	public ICompletionProposal[] computeCompletionProposals(
			ITextViewer viewer, int offset) {
		fProposals.clear();
		SVDocumentTextScanner scanner = new SVDocumentTextScanner(
				viewer.getDocument(), offset);
		
		int lineno = -1;
		
		try {
			lineno = viewer.getDocument().getLineOfOffset(offset);
		} catch (BadLocationException e) {
			e.printStackTrace();
			return new ICompletionProposal[0];
		}
		
		computeProposals(scanner, fEditor.getSVDBFile(), lineno);
		
		// convert SVProposal list to ICompletionProposal list
		for (SVCompletionProposal p : fCompletionProposals) {
			List<ICompletionProposal> cp = convertToProposal(p, viewer.getDocument()); 
 
			fProposals.addAll(cp);
		}
		
		
		return fProposals.toArray(new ICompletionProposal[fProposals.size()]);
	}
	
	protected List<ICompletionProposal> convertToProposal(
			SVCompletionProposal		p,
			IDocument					doc) {
		List<ICompletionProposal> 	ret = new ArrayList<ICompletionProposal>();
		ICompletionProposal 		cp = null;
		String prefix = p.getPrefix();
		int replacementOffset = p.getReplacementOffset();
		int replacementLength = p.getReplacementLength();
		
		if (p.getItem() != null) {
			SVDBItem it = p.getItem();
			switch (p.getItem().getType()) {
				case Function:
				case Task: 
					cp = createTaskFuncProposal(
							it, doc, replacementOffset, replacementLength);
					break;
		
				case Macro:
					cp = createMacroProposal(
							it, doc, replacementOffset, replacementLength);
					break;
		
				case Class:
					cp = createClassProposal(
							it, doc, replacementOffset, replacementLength);
					break;
					
				case Typedef: {
					SVDBTypedef td = (SVDBTypedef)it;
					String td_name_lc = td.getName().toLowerCase();
					String prefix_lc  = prefix.toLowerCase();
					
					// If we matched the typename, then construct a typedef
					// proposal.
					if (prefix.equals("") || td_name_lc.startsWith(prefix_lc)) {
						cp = new CompletionProposal(it.getName(),
								replacementOffset, replacementLength, 
								it.getName().length(), SVDBIconUtils.getIcon(it),
								null, null, null);
						ret.add(cp);
					}
					
					// Check to see if the name matches any enum values
					if (td.getTypeInfo().getDataType() == SVDBDataType.Enum) {
						SVDBTypeInfoEnum enum_t = (SVDBTypeInfoEnum)td.getTypeInfo();
						
						for (Tuple<String, String> n : enum_t.getEnumValues()) {
							String name = n.first();
							String name_lc = n.first().toLowerCase();
							if (prefix.equals("") || name_lc.startsWith(prefix_lc)) {
								String label = td.getName() + "::" + name;
								cp = new CompletionProposal(name,
										replacementOffset, replacementLength, 
										name.length(),
										SVDBIconUtils.getIcon(ISVIcons.ENUM_TYPE_OBJ),
										label, null, null);
								ret.add(cp);
							}
						}
					}
					cp = null;
				} break;
				
				case PackageDecl: {
					String import_all = it.getName() + "::*;";
					cp = new CompletionProposal(it.getName(),
							replacementOffset, replacementLength, 
							it.getName().length(), SVDBIconUtils.getIcon(it),
							null, null, null);
					ret.add(cp);
					cp = new CompletionProposal(import_all, 
							replacementOffset, replacementLength, 
							import_all.length(), SVDBIconUtils.getIcon(it),
							null, null, null);
				} break;
		
				default:
					cp = new CompletionProposal(it.getName(),
							replacementOffset, replacementLength, 
							it.getName().length(), SVDBIconUtils.getIcon(it),
							null, null, null);
					break;
			}
		} else if (p.getType() == SVCompletionProposalType.Keyword) {
			cp = new CompletionProposal(p.getReplacement(), 
					p.getReplacementOffset(), p.getReplacementLength(), 
					p.getReplacement().length(), SVUiPlugin.getImage("/icons/edecl16/keyword_obj.gif"), null, null, null);
		} else {
			cp = new CompletionProposal(p.getReplacement(), 
					p.getReplacementOffset(), p.getReplacementLength(), 
					p.getReplacement().length());
		}
		
		if (cp != null) {
			ret.add(cp);
		}

		return ret;
	}
	
	private String escapeId(String id) {
		StringBuilder sb = new StringBuilder(id);
		for (int i=0; i<sb.length(); i++) {
			if (sb.charAt(i) == '$') {
				sb.insert(i, '$');
				i++;
			}
		}
		return sb.toString();
	}
	
	private ICompletionProposal createTaskFuncProposal(
			SVDBItem 					it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBTaskFuncScope tf = (SVDBTaskFuncScope)it;
		
		d.append(it.getName() + "(");
		r.append(escapeId(it.getName()) + "(");
		
		for (int i=0; i<tf.getParams().size(); i++) {
			SVDBParamPort param = tf.getParams().get(i);
			
			d.append(param.getTypeName() + " " + param.getName());
			r.append("${");
			r.append(param.getName());
			r.append("}");
			
			if (i+1 < tf.getParams().size()) {
				d.append(", ");
				r.append(", ");
			}
		}
		d.append(")");
		r.append(")");
		
		if (it.getType() == SVDBItemType.Function &&
				tf.getReturnType() != null &&
				!tf.getReturnType().equals("void") &&
				!it.getName().equals("new")) {
			d.append(" : ");
			d.append(tf.getReturnType());
		}
		
		// Find the class that this function belongs to (if any)
		SVDBItem class_it = it;
		
		while (class_it != null && class_it.getType() != SVDBItemType.Class) {
			class_it = class_it.getParent();
		}
		
		String cls_name = null;
		if (class_it != null) {
			cls_name = class_it.getName();
			if (cls_name.equals("__sv_builtin_queue")) {
				cls_name = "[$]";
			} else if (cls_name.equals("__sv_builtin_array")) {
				cls_name = "[]";
			} else if (cls_name.equals("__sv_builtin_assoc_array")) {
				cls_name = "[*]";
			} else if (cls_name.startsWith("__sv_builtin")) {
				cls_name = cls_name.substring("__sv_builtin".length());
			}
		}

		Template t = new Template(d.toString(), 
				(cls_name != null)?cls_name:"", "CONTEXT",
				r.toString(), (tf.getParams().size() == 0));
		
		return new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));
	}

	private ICompletionProposal createMacroProposal(
			SVDBItem 					it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		fLog.debug("createMacroProposal: " + it.getName());

		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBMacroDef md = (SVDBMacroDef)it;

		d.append(it.getName());
		r.append(it.getName());
		if (md.getParameters().size() > 0) {
			d.append("(");
			r.append("(");
		}
		
		for (int i=0; i<md.getParameters().size(); i++) {
			String param = md.getParameters().get(i);
			
			d.append(param);
			r.append("${");
			r.append(param);
			r.append("}");
			
			if (i+1 < md.getParameters().size()) {
				d.append(", ");
				r.append(", ");
			}
		}
		
		if (md.getParameters().size() > 0) {
			d.append(")");
			r.append(")");
		}
		
		Template t = new Template(d.toString(), "", "CONTEXT",
				r.toString(), true);
		
		return new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));
	}

	private ICompletionProposal createClassProposal(
			SVDBItem 					it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBModIfcClassDecl cl = (SVDBModIfcClassDecl)it;
		
		r.append(it.getName());
		d.append(it.getName());
		
		if (cl.getParameters().size() > 0) {
			r.append(" #(");
			for (int i=0; i<cl.getParameters().size(); i++) {
				SVDBModIfcClassParam pm = cl.getParameters().get(i);

				r.append("${");
				r.append(pm.getName());
				r.append("}");
				
				if (i+1 < cl.getParameters().size()) {
					r.append(", ");
				}
			}
			r.append(")");
		}

		Template t = new Template(
				d.toString(), "", "CONTEXT", r.toString(), true);
		
		return new TemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				SVDBIconUtils.getIcon(it));
	}

	@Override
	protected ISVDBIndexIterator getIndexIterator() {
		return fEditor.getIndexIterator();
	}

	@Override
	protected SVDBFile getSVDBFile() {
		return fEditor.getSVDBFile();
	}


	/**
	 * Add a proposal to the proposals list, ensure that this proposal isn't a
	 * duplicate
	 * 
	 * @param p
	 * @param proposals
	private static void addProposal(ICompletionProposal p,
			List<ICompletionProposal> proposals) {
		boolean found = false;

		for (ICompletionProposal p_t : proposals) {
			if (p.getDisplayString().equals(p_t.getDisplayString())) {
				found = true;
				break;
			}
		}

		if (!found) {
			proposals.add(p);
		}
	}
	 */
	
	public IContextInformation[] computeContextInformation(
			ITextViewer viewer, int offset) {
		
		return NO_CONTEXTS;
	}

	public char[] getCompletionProposalAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	public char[] getContextInformationAutoActivationCharacters() {
		return PROPOSAL_ACTIVATION_CHARS;
	}

	public IContextInformationValidator getContextInformationValidator() {
		System.out.println("getContextInformationValidator()");
		// TODO Auto-generated method stub
		return null;
	}

	public String getErrorMessage() {
		// TODO Auto-generated method stub
		return null;
	}
	
}

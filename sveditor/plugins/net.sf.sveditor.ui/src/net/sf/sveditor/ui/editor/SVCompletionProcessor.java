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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.content_assist.AbstractCompletionProcessor;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.content_assist.SVCompletionProposalType;
import net.sf.sveditor.core.content_assist.SVCompletionProposalUtils;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.job_mgr.IJob;
import net.sf.sveditor.core.job_mgr.IJobMgr;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.preference.IPreferenceStore;
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
import org.eclipse.swt.widgets.Display;


public class SVCompletionProcessor extends AbstractCompletionProcessor 
		implements IContentAssistProcessor {

	private SVEditor 						fEditor;
	private SVCompletionProposalUtils		fProposalUtils;
	private static final boolean			fShowModulePorts = false;

	private static final char[] PROPOSAL_ACTIVATION_CHARS = { '.', ':' };
	private final IContextInformation NO_CONTEXTS[] = new IContextInformation[0];
	
	private List<ICompletionProposal>				fProposals = 
		new ArrayList<ICompletionProposal>();

	public SVCompletionProcessor(SVEditor editor) {
		fLog = LogFactory.getLogHandle("SVCompletionProcessor");
		fEditor = editor;
		fProposalUtils = new SVCompletionProposalUtils();
	}
	
	public ICompletionProposal[] computeCompletionProposals(
			ITextViewer viewer, int offset) {
		fProposalUtils.setTFMaxCharsPerLine(SVUiPlugin.getDefault().getIntegerPref(
				SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_LINE_WRAP_LIMIT));
		fProposalUtils.setTFNamedPorts(SVUiPlugin.getDefault().getBooleanPref(
				SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_NAMED_PORTS_EN));
		fProposalUtils.setTFPortsPerLine(SVUiPlugin.getDefault().getIntegerPref(
				SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_MAX_PARAMS_PER_LINE));

		fProposalUtils.setModIfcInstMaxCharsPerLine(
				SVUiPlugin.getDefault().getIntegerPref(
						SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_LINE_WRAP_LIMIT));
		fProposalUtils.setModIfcInstNamedPorts(
				SVUiPlugin.getDefault().getBooleanPref(
						SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_NAMED_PORTS_EN));
		fProposalUtils.setModIfcInstPortsPerLine(
				SVUiPlugin.getDefault().getIntegerPref(
						SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_MAX_PORTS_PER_LINE));

		fProposals.clear();
		final SVDocumentTextScanner scanner = new SVDocumentTextScanner(
				viewer.getDocument(), offset);
		scanner.setSkipComments(true);
		
		int lineno = -1, linepos = -1;
		
		
		try {
			lineno = viewer.getDocument().getLineOfOffset(offset);
			linepos = (offset-viewer.getDocument().getLineOffset(lineno));
		} catch (BadLocationException e) {
			e.printStackTrace();
			return new ICompletionProposal[0];
		}

		IJobMgr job_mgr = SVCorePlugin.getJobMgr();
		IJob job = job_mgr.createJob();
		final int lineno_f = lineno, linepos_f = linepos;
		job.init("Content Assist", new Runnable() {
			public void run() {
				computeProposals(scanner, fEditor.getSVDBFile(), lineno_f, linepos_f);
			}
		});
		
		job_mgr.queueJob(job);
		
		// Now, wait for the job to complete
		Display d = Display.getCurrent();
		int wait_time_ms = 1;
		IPreferenceStore p_store = SVUiPlugin.getDefault().getPreferenceStore();
		int timeout_ms = p_store.getInt(SVEditorPrefsConstants.P_CONTENT_ASSIST_TIMEOUT);
		int timeout_remain = timeout_ms;
		
		while (true) {
			if (job.join(wait_time_ms)) {
				break;
			}
			if (timeout_ms != 0) {
				timeout_remain -= wait_time_ms;

				if (timeout_remain < 0) {
					break;
				}
			}
			while (d.readAndDispatch()) { }
		}
	
		List<SVCompletionProposal> temp_p = new ArrayList<SVCompletionProposal>();
		if (fCompletionProposals == null) {
			fCompletionProposals = new ArrayList<SVCompletionProposal>();
		}
		synchronized (fCompletionProposals) {
			temp_p.addAll(fCompletionProposals);
		}
		
		// convert SVProposal list to ICompletionProposal list
		for (SVCompletionProposal p : temp_p) {
			List<ICompletionProposal> cp = convertToProposal(p, viewer.getDocument()); 

			fProposals.addAll(cp);
		}
	
		return fProposals.toArray(new ICompletionProposal[fProposals.size()]);	
	}
	
	private static int getIndentStringSize(String indent) {
		int size=0;
		for (int i=0; i<indent.length(); i++) {
			if (indent.charAt(i) == '\t') {
				size += SVUiPlugin.getDefault().getTabWidth();
			} else {
				size++;
			}
		}
		return size;
	}
	
	protected List<ICompletionProposal> convertToProposal(
			SVCompletionProposal		p,
			IDocument					doc) {
		List<ICompletionProposal> 	ret = new ArrayList<ICompletionProposal>();
		ICompletionProposal 		cp = null;
		String prefix = p.getPrefix();
		int replacementOffset = p.getReplacementOffset();
		int replacementLength = p.getReplacementLength();
		
		// Patch up to ensure the replacement offset doesn't extend beyond the document
		if (replacementOffset > doc.getLength()) {
			replacementOffset = doc.getLength();
		}
		
		String doc_str = "";
		try {
			doc_str = doc.get(0, replacementOffset);
		} catch (BadLocationException e) {}
		
		String next_line_indent = SVCompletionProposalUtils.getLineIndent(
				doc_str, SVUiPlugin.getDefault().getIndentIncr());
		int first_line_pos = getIndentStringSize(next_line_indent);
		next_line_indent += SVUiPlugin.getDefault().getIndentIncr();
		int subseq_line_pos = getIndentStringSize(next_line_indent);
		
		if (p.getItem() != null) {
			ISVDBItemBase it = p.getItem();
			switch (p.getItem().getType()) {
				case Function:
				case Task: 
					cp = createTaskFuncProposal(
							it, doc, replacementOffset, replacementLength,
							next_line_indent, first_line_pos, subseq_line_pos);
					break;
		
				case ModuleDecl:
					cp = createModuleProposal(
							it, doc, replacementOffset, replacementLength,
							next_line_indent, first_line_pos, subseq_line_pos);
					break;

				case MacroDef:
					cp = createMacroProposal(
							it, doc, replacementOffset, replacementLength);
					break;
		
				case ClassDecl:
					cp = createClassProposal(
							it, doc, replacementOffset, replacementLength);
					break;
					
				case TypedefStmt: {
					SVDBTypedefStmt tds = (SVDBTypedefStmt)it;
					String td_name_lc = tds.getName().toLowerCase();
					String prefix_lc  = prefix.toLowerCase();
					
					// If we matched the typename, then construct a typedef
					// proposal.
					if (prefix.equals("") || td_name_lc.startsWith(prefix_lc)) {
						cp = new CompletionProposal(SVDBItem.getName(it),
								replacementOffset, replacementLength, 
								SVDBItem.getName(it).length(), SVDBIconUtils.getIcon(it),
								null, null, null);
						ret.add(cp);
					}
					
					// Check to see if the name matches any enum values
					/** TODO:
					if (tds.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
						SVDBTypeInfoEnum enum_t = (SVDBTypeInfoEnum)tds.getTypeInfo();
						
						Tuple<List<String>, List<String>> enums = enum_t.getEnumValues(); 

						for (String name : enums.first()) {
							String name_lc = name.toLowerCase();
							if (prefix.equals("") || name_lc.startsWith(prefix_lc)) {
								String label = tds.getName() + "::" + name;
								cp = new CompletionProposal(name,
										replacementOffset, replacementLength, 
										name.length(),
										SVDBIconUtils.getIcon(ISVIcons.ENUM_TYPE_OBJ),
										label, null, null);
								ret.add(cp);
							}
						}
					}
					 */
					cp = null;
				} break;
				
				case PackageDecl: {
					String import_all = SVDBItem.getName(it) + "::*;";
					cp = new CompletionProposal(SVDBItem.getName(it),
							replacementOffset, replacementLength, 
							SVDBItem.getName(it).length(), SVDBIconUtils.getIcon(it),
							null, null, null);
					ret.add(cp);
					cp = new CompletionProposal(import_all, 
							replacementOffset, replacementLength, 
							import_all.length(), SVDBIconUtils.getIcon(it),
							null, null, null);
				} break;
				
				case VarDeclItem: {
					cp = createVarItemProposal(
							it, doc, replacementOffset, replacementLength);					
				} break;
		
				default:
					cp = new CompletionProposal(SVDBItem.getName(it),
							replacementOffset, replacementLength, 
							SVDBItem.getName(it).length(), SVDBIconUtils.getIcon(it),
							null, null, null);
					break;
			}
		} else if (p.getType() == SVCompletionProposalType.Keyword) {
			cp = new CompletionProposal(p.getReplacement(), 
					p.getReplacementOffset(), p.getReplacementLength(), 
					p.getReplacement().length(), SVUiPlugin.getImage("/icons/edecl16/keyword_obj.gif"), null, null, null);
		} else if (p.getType() == SVCompletionProposalType.Include) {
			cp = new CompletionProposal(p.getReplacement(), 
					p.getReplacementOffset(), p.getReplacementLength(), 
					p.getReplacement().length(), 
					SVUiPlugin.getImage("/icons/edecl16/include_obj.gif"), 
					p.getDisplayString(), 
					null, 
					p.getAdditionalInfo());
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
	
	private ICompletionProposal createTaskFuncProposal(
			ISVDBItemBase 				it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength,
			String						next_line_indent,
			int							first_line_pos,
			int							subseq_line_pos) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		StringBuilder d = new StringBuilder();		// help text
		SVDBTask tf = (SVDBTask)it;
		
		d.append(SVDBItem.getName(it) + "(");
		
		ArrayList<String> all_types = new ArrayList<String> ();
		ArrayList<String> all_ports = new ArrayList<String> ();
		for (int i=0; i<tf.getParams().size(); i++) {
			SVDBParamPortDecl param = tf.getParams().get(i);
			for (ISVDBChildItem c : param.getChildren()) {
				SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
				all_ports.add(vi.getName());
				all_types.add(param.getTypeName());
			}
		}

		// Now create the string & port list - note that we are padding to the longest string with spaces
		for (int i=0; i<all_ports.size(); i++)  {
			d.append(all_types.get(i) + " " + all_ports.get(i));
	
			// Only add ", " on all but the last parameters
			if (i+1 < all_ports.size())  {
				d.append(", ");
			}
		}
		
		// Close the function instantiation
		d.append(")");
		
		if (it.getType() == SVDBItemType.Function) {
			SVDBFunction f = (SVDBFunction)tf;
			if (f.getReturnType() != null &&
				!f.getReturnType().equals("void") &&
				!SVDBItem.getName(it).equals("new")) {
				d.append(" : ");
				d.append(f.getReturnType());
			}
		}
		
		// Find the class that this function belongs to (if any)
		ISVDBChildItem class_it = (ISVDBChildItem)it;
		
		while (class_it != null && class_it.getType() != SVDBItemType.ClassDecl) {
			class_it = class_it.getParent();
		}
		
		String cls_name = null;
		if (class_it != null && class_it instanceof ISVDBNamedItem) {
			cls_name = ((ISVDBNamedItem)class_it).getName();
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
		
		// TODO:
		String template_str = fProposalUtils.createTFTemplate(tf, 
				next_line_indent, first_line_pos, subseq_line_pos);

		Template t = new Template(d.toString(), 
				(cls_name != null)?cls_name:"", "CONTEXT",
				template_str, (tf.getParams().size() == 0));
		
		return new SVTemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				getIndexIterator(), it);
	}

	private ICompletionProposal createModuleProposal(
			ISVDBItemBase 				it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength,
			String						next_line_indent,
			int							first_line_pos,
			int							subseq_line_pos) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		StringBuilder d = new StringBuilder();		// help text
		SVDBModIfcDecl tf = (SVDBModIfcDecl)it;
		
		d.append(SVDBItem.getName(it));

		if (fShowModulePorts) {
			d.append("(");
		
			ArrayList<String> all_types = new ArrayList<String> ();
			ArrayList<String> all_ports = new ArrayList<String> ();
			for (int i=0; i<tf.getPorts().size(); i++) {
				SVDBParamPortDecl param = tf.getPorts().get(i);
				for (ISVDBChildItem c : param.getChildren()) {
					SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
					all_ports.add(vi.getName());

					if (param.getTypeInfo() == null) {
						all_types.add(null);
					} else {
						all_types.add(param.getTypeName());
					}
				}
			}

			// Now create the string & port list - note that we are padding to the longest string with spaces
			for (int i=0; i<all_ports.size(); i++)  {
				if (all_types.get(i) == null) {
					d.append(all_ports.get(i));
				} else {
					d.append(all_types.get(i) + " " + all_ports.get(i));
				}

				// Only add ", " on all but the last parameters
				if (i+1 < all_ports.size())  {
					d.append(", ");
				}
			}

			// Close the function instantiation
			d.append(")");
		}
		
		// TODO:
		String template_str = fProposalUtils.createModuleTemplate(tf, 
				next_line_indent, first_line_pos, subseq_line_pos);

		
		Template t = new Template(d.toString(), "", "CONTEXT",
				template_str, (tf.getPorts().size() == 0));
		
		return new SVTemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				getIndexIterator(), it);
	}

	private ICompletionProposal createMacroProposal(
			ISVDBItemBase 				it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		fLog.debug("createMacroProposal: " + SVDBItem.getName(it));

		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBMacroDef md = (SVDBMacroDef)it;

		d.append(SVDBItem.getName(it));
		r.append(SVDBItem.getName(it));
		if (md.getParameters() != null &&
				md.getParameters().size() > 0) {
			d.append(" (");
			r.append(" (");
			
			for (int i=0; i<md.getParameters().size(); i++) {
				String param = md.getParameters().get(i).getName();

				d.append(param);
				r.append("${");
				r.append(param);
				r.append("}");

				if (i+1 < md.getParameters().size()) {
					d.append(", ");
					r.append(",\n");
				}
			}

			d.append(")");
			r.append(")");
		}
		
		Template t = new Template(d.toString(), "", "CONTEXT",
				r.toString(), true);
		
		return new SVTemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				getIndexIterator(), it);
	}

	private ICompletionProposal createClassProposal(
			ISVDBItemBase 				it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBClassDecl cl = (SVDBClassDecl)it;
		
		r.append(SVDBItem.getName(it));
		d.append(SVDBItem.getName(it));
		
		if (cl.getParameters() != null && cl.getParameters().size() > 0) {
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
		
		return new SVTemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				getIndexIterator(), it);
	}

	private ICompletionProposal createVarItemProposal(
			ISVDBItemBase 				it,
			IDocument					doc,
			int							replacementOffset,
			int							replacementLength) {
		TemplateContext ctxt = new DocumentTemplateContext(
				new TemplateContextType("CONTEXT"),
				doc, replacementOffset, replacementLength);
		
		StringBuilder d = new StringBuilder();
		StringBuilder r = new StringBuilder();
		SVDBVarDeclItem var = (SVDBVarDeclItem)it;
		
		r.append(SVDBItem.getName(it));
		d.append(SVDBItem.getName(it));
	
		/*
		if (cl.getParameters() != null && cl.getParameters().size() > 0) {
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
		 */
	
		String description = "";
		if (var.getParent() != null) {
			SVDBVarDeclStmt var_stmt = (SVDBVarDeclStmt)var.getParent();
			if (var_stmt.getTypeInfo() != null) {
				d.append(" : " + var_stmt.getTypeInfo().toString());
			}
			
			if (var_stmt.getParent() != null && 
					var_stmt.getParent().getType() == SVDBItemType.ClassDecl) {
				description = SVDBItem.getName(var_stmt.getParent());
			}
		}

		Template t = new Template( d.toString(), description, 
				"CONTEXT", r.toString(), true);
		
		return new SVTemplateProposal(t, ctxt,
				new Region(replacementOffset, replacementLength), 
				getIndexIterator(), it);
	}

	@Override
	protected ISVDBIndexIterator getIndexIterator() {
		return fEditor.getIndexIterator();
	}

	@Override
	protected SVDBFile getSVDBFile() {
		return fEditor.getSVDBFile();
	}

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

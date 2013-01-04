package net.sf.sveditor.core.argfile.content_assist;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.argfile.parser.ISVArgFileOptionProvider.OptionType;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileDefaultOptionProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileExprContext;
import net.sf.sveditor.core.argfile.parser.SVArgFileExprContext.ContextType;
import net.sf.sveditor.core.argfile.parser.SVArgFileExprScanner;
import net.sf.sveditor.core.argfile.parser.SVArgFileUtils;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

import org.eclipse.core.resources.IProject;

public class AbstractArgFileCompletionProcessor implements ILogLevel {
	protected List<SVArgFileCompletionProposal>			fProposals;
	protected LogHandle									fLog;
	protected ISVDBFileSystemProvider					fFileSystemProvider;
	protected String									fBaseLocationDir;
	protected IProject									fProject;
	protected ISVArgFileVariableProvider				fVarProvider;
	
	public AbstractArgFileCompletionProcessor(LogHandle log) {
		fProposals = new ArrayList<SVArgFileCompletionProposal>();
		fLog = log;
	}
	
	public void init(
			ISVDBFileSystemProvider				fs_provider,
			String								base_location_dir,
			IProject							project,
			ISVArgFileVariableProvider			vp) {
		fFileSystemProvider = fs_provider;
		fBaseLocationDir = base_location_dir;
		fProject = project;
		fVarProvider = vp;
	}
	
	public List<SVArgFileCompletionProposal> getProposals() {
		return fProposals;
	}

	public void computeProposals(
			IBIDITextScanner		scanner,
			int						lineno,
			int						linepos) {
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, false);
		SVArgFileDefaultOptionProvider op = new SVArgFileDefaultOptionProvider();
		
		fProposals.clear();
		
		if (ctxt.fType == ContextType.PathComplete) {
			boolean is_file_path = true;
			
			if (ctxt.fRoot != null) {
				// Determine whether we need to do 
				// directory completion instead
				OptionType op_type = op.getOptionType(ctxt.fRoot);
				if (op_type == OptionType.Incdir ||
						op_type == OptionType.SrcLibPath) {
					is_file_path = false;
				}
			}
			
			computePathProposals(ctxt, is_file_path);
		} else if (ctxt.fType == ContextType.OptionComplete) {
			// TODO:
		} else {
			// Unknown 
		}
	}
	
	protected void computePathProposals(
			SVArgFileExprContext		ctxt, 
			boolean						is_file_path) {
		boolean var_request = false;
		boolean var_brace_delimited = false;
		String resolved_base = null;
		String proposal_base = "";
		String proposal_leaf = "";
		
		if (ctxt.fLeaf != null && !ctxt.fLeaf.trim().equals("")) {
			// Completion with a path specified
			
			// Determine whether this is really a variable-completion request
			int idx = ctxt.fLeaf.lastIndexOf('$');
			
			if (idx != -1) {
				if (idx+1 < ctxt.fLeaf.length() &&
						ctxt.fLeaf.charAt(idx+1) == '{') {
					// have an unterminated ${...} variable reference
					var_request = (ctxt.fLeaf.indexOf('}', idx+1) == -1);
					var_brace_delimited = true;
					proposal_leaf = ctxt.fLeaf.substring(idx+2);
				} else if (ctxt.fLeaf.indexOf('/', idx+1) == -1 &&
						ctxt.fLeaf.indexOf('\\', idx+1) == -1) {
					// have an unterminated $... variable reference
					var_request = true;
					// If the variable request is just '$'
					if (idx+1 >= ctxt.fLeaf.length()) {
						var_brace_delimited = true;
					}
					proposal_leaf = ctxt.fLeaf.substring(idx+1);
				}
			}
			
			if (!var_request) {
				if (ctxt.fLeaf.endsWith("/")) {
					// no leaf supplied
					proposal_base = ctxt.fLeaf;
					proposal_leaf = "";
				} else {
					// Leaf path supplied
					proposal_base = SVFileUtils.getPathParent(ctxt.fLeaf) + "/";
					proposal_leaf = SVFileUtils.getPathLeaf(ctxt.fLeaf);
				}
				
				resolved_base = SVArgFileUtils.expandVars(proposal_base, fVarProvider);

				/*
				proposal = proposal_base + full_file.substring(resolved_base.length());
				proposal = SVFileUtils.getPathParent(proposal_base) + "/" + file;
				 */
				
				if (!fFileSystemProvider.isDir(resolved_base)) {
					resolved_base = SVArgFileUtils.expandVars(
							fBaseLocationDir + "/" + proposal_base, fVarProvider);
				}
			}
		} else {
			// Completion without a path specified
			resolved_base = fBaseLocationDir;
		}
		
		if (var_request) {
			for (String var : fVarProvider.getVariables()) {
				if (matches(var, proposal_leaf)) {
					String proposal;
					
					if (var_brace_delimited) {
						proposal = "${" + var + "}";
					} else {
						proposal = "$" + var;
					}
				
					addProposal(ctxt, proposal);
				}
			}
		} else {
			if (fFileSystemProvider.isDir(resolved_base)) {
				List<String> files = fFileSystemProvider.getFiles(resolved_base);

				for (String full_file : files) {
					String file = SVFileUtils.getPathLeaf(full_file);
					String proposal;
					
					/*
					if (proposal_base.equals("")) {
						proposal = full_file.substring(resolved_base.length());
					} else {
						proposal = proposal_base + full_file.substring(resolved_base.length());
					}
					 */
					/*
					proposal = proposal_base + full_file.substring(resolved_base.length());
					proposal = SVFileUtils.getPathParent(proposal_base) + "/" + file;
					 */
					proposal = proposal_base + file;
					
					fLog.debug("file path: " + file);
					if (is_file_path) {
						// File path -- accept file or dir
						if (matches(file, proposal_leaf)) {
							addProposal(ctxt, proposal);
						}
					} else {
						// Dir path
						if (fFileSystemProvider.isDir(file)) {
							if (matches(file, proposal_leaf)) {
								addProposal(ctxt, proposal);
							}
						}
					}
				}
			} else {
				fLog.debug("[ERROR] resolved_base doesn't exist: " + resolved_base);
			}
		}
	}

	private boolean matches(String name, String pattern) {
		return (pattern.equals("") ||
				name.toLowerCase().startsWith(pattern.toLowerCase()));
	}
	
	protected void addProposal(SVArgFileExprContext ctxt, String replacement) {
		addProposal(new SVArgFileCompletionProposal(ctxt.fLeaf, replacement, 
				ctxt.fStart, ctxt.fLeaf.length()));
	}
	
	protected void addProposal(SVArgFileCompletionProposal proposal) {
		if (!fProposals.contains(proposal)) {
			fProposals.add(proposal);
		}
	}
}

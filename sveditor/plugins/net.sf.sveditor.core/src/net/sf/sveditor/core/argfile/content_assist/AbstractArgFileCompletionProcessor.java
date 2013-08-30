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
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;

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
		String pathsep = "/";
		
		fLog.debug("leaf=" + ctxt.fLeaf + " root=" + ctxt.fRoot);
		
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
				// Determine what to use at the resolved_base
				if (ctxt.fLeaf.indexOf('/') != -1 ||
						ctxt.fLeaf.indexOf('\\') != -1) {
					// It makes sense to provide proposals from the parent
					
					if (ctxt.fLeaf.endsWith("/") || ctxt.fLeaf.endsWith("\\")) {
						// Proposal request doesn't really have a leaf
						proposal_base = ctxt.fLeaf;
						proposal_leaf = "";
						resolved_base = ctxt.fLeaf;
						pathsep = "" + ctxt.fLeaf.charAt(ctxt.fLeaf.length()-1);
					} else {
						// Proposal request does have a leaf. We should resolve
						// relative to the base of the leaf
						proposal_base = SVFileUtils.getPathParent(ctxt.fLeaf) + "/";
						proposal_leaf = SVFileUtils.getPathLeaf(ctxt.fLeaf);
						resolved_base = SVFileUtils.getPathParent(ctxt.fLeaf);
					}
				
					resolved_base = SVFileUtils.resolvePath(
							SVArgFileUtils.expandVars(resolved_base, fVarProvider),
							fBaseLocationDir, fFileSystemProvider, true);

					if (!fFileSystemProvider.isDir(resolved_base)) {
						// Try prepending the base location
						String tmp_resolved_base = fBaseLocationDir + "/" + resolved_base;
					
						if (fFileSystemProvider.isDir(tmp_resolved_base)) {
							resolved_base = tmp_resolved_base;
						} else {
							fLog.debug("Neither resolved_base=" + resolved_base + 
									" nor tmp_resolved_base=" + tmp_resolved_base + " exist");
						}
					}
				} else {
					// We should just use the supplied BaseLocation
					proposal_base = "";
					proposal_leaf = ctxt.fLeaf;
					resolved_base = fBaseLocationDir;
				}

				fLog.debug("initial resolved_base: " + resolved_base);
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
			int last_sl;
			
			if ((last_sl = resolved_base.lastIndexOf('/')) == -1) {
				last_sl = resolved_base.lastIndexOf('\\');
			}
			
			if (fFileSystemProvider.isDir(resolved_base)) {
				List<String> files = fFileSystemProvider.getFiles(resolved_base);

				for (String full_file : files) {
					String file = SVFileUtils.getPathLeaf(full_file);
					String proposal;
					
					proposal = proposal_base + file;
					
					fLog.debug("file path: " + file);
					if (is_file_path) {
						// File path -- accept file or dir
						if (matches(file, proposal_leaf)) {
							addProposal(ctxt, proposal);
						}
					} else {
						// Dir path
						if (fFileSystemProvider.isDir(full_file) &&
								!file.startsWith(".")) { // Filter out resources (eg .svn)
							if (matches(file, proposal_leaf)) {
								addProposal(ctxt, proposal);
							}
						}
					}
				}
			} else if (resolved_base.equals("${workspace_loc}")) {
				// List projects
				IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
				
				for (IProject p : root.getProjects()) {
					if (matches(p.getName(), proposal_leaf)) {
						addProposal(ctxt, resolved_base + pathsep + p.getName());
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

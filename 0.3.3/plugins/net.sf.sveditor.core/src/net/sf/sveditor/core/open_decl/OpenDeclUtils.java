package net.sf.sveditor.core.open_decl;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBOpenDeclarationIncludeNameMatcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.expr_utils.SVExprScanner;
import net.sf.sveditor.core.expr_utils.SVExpressionUtils;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class OpenDeclUtils {
	
	public static List<Tuple<SVDBItem, SVDBFile>> openDecl(
			SVDBFile			file,
			int					line,
			IBIDITextScanner	scanner,
			ISVDBIndexIterator	index_it) {
		LogHandle log = LogFactory.getLogHandle("OpenDeclaration");
		SVExpressionUtils		expr_utils = new SVExpressionUtils(new SVDBFindDefaultNameMatcher());
		SVExprScanner			expr_scanner = new SVExprScanner();
		SVDBItem it = null;
		SVDBFile inc_file = null;
		
		SVExprContext expr_ctxt = expr_scanner.extractExprContext(scanner, true);
		
		log.debug("Expression Context: root=" + expr_ctxt.fRoot +
				" trigger=" + expr_ctxt.fTrigger + " leaf=" + expr_ctxt.fLeaf);
		
		ISVDBScopeItem active_scope = 
			SVDBSearchUtils.findActiveScope(file, line);
		
		// If this is an include lookup, then use a different matching strategy
		if (expr_ctxt.fTrigger != null && expr_ctxt.fRoot != null &&
				expr_ctxt.fTrigger.equals("`") && expr_ctxt.fRoot.equals("include")) {
			expr_utils.setMatcher(new SVDBOpenDeclarationIncludeNameMatcher());
		}

		List<Tuple<SVDBItem, SVDBFile>> ret = new ArrayList<Tuple<SVDBItem,SVDBFile>>();
		
		List<SVDBItem> items = expr_utils.findItems(index_it, active_scope, expr_ctxt, false);
		
		if (items.size() > 0) {
			it = items.get(0);
			
			// Confused here...
			ret.add(new Tuple<SVDBItem, SVDBFile>(it, inc_file));
		}
		
		return ret;
	}

}

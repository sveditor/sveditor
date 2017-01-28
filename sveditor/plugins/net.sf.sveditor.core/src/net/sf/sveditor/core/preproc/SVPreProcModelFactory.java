package net.sf.sveditor.core.preproc;

import java.io.InputStream;
import java.util.Stack;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.preproc.PreProcEvent.Type;

/**
 * Used to construct 
 * @author ballance
 *
 */
public class SVPreProcModelFactory implements IPreProcListener {
	private ISVStringPreProcessor			fPreProc;
	private Stack<SVPreProcModelNode>		fModelStack;
	private SVPreProcModelNode				fRoot;
	
	public SVPreProcModelFactory(ISVStringPreProcessor preproc) {
		fPreProc = preproc;
		fModelStack = new Stack<SVPreProcModelNode>();
	}
	
	public Tuple<SVPreProcModelNode, String> build(InputStream in) {
		fModelStack.clear();
		fRoot = null;
	
		fPreProc.setEmitLineDirectives(false);
		fPreProc.addListener(this);
		String result = fPreProc.preprocess(in);
		fPreProc.removeListener(this);
		
		// Traverse event stack to build the expansion model 
		
		return new Tuple<SVPreProcModelNode, String>(fRoot, result);
	}
	
	public Tuple<SVPreProcModelNode, String> build(String in) {
		return build(new StringInputStream(in));
	}

	@Override
	public void preproc_event(PreProcEvent event) {
		if (event.type == Type.BeginExpand) {
//			fEventStack.push(event);
			SVPreProcModelNode n = new SVPreProcModelNode(event.text, event.pos);
			
			// Add a new child node
			fModelStack.push(n);
		} else if (event.type == Type.EndExpand) {
			SVPreProcModelNode n = fModelStack.pop();
			n.setEnd(event.pos);
			if (fModelStack.size() > 0) {
				fModelStack.peek().add(n);
			} else {
				fRoot = n;
			}
//			PreProcEvent ev = fEventStack.pop();
//			fExtents.add(new Tuple<Integer, Integer>(ev.pos, event.pos));
		}
	}

}

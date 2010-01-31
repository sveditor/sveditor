package net.sf.sveditor.core.indent;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class SVDefaultIndenter implements ISVIndenter {
	enum State {
		
	};
	private ISVIndentScanner				fScanner;
	private List<SVIndentToken>				fFormatQueue;
	private Stack<String>					fIndentStack;
	
	public SVDefaultIndenter() {
		fFormatQueue = new ArrayList<SVIndentToken>();
		fIndentStack = new Stack<String>();
	}
	
	public void init(ISVIndentScanner scanner) {
		fScanner = scanner;
		fIndentStack.push("");
	}

	public void indent(SVIndentToken token) {
		/*
		System.out.println("Token \"" + token.getImage() + 
				"\" isStartLine: " + token.isStartLine() +
				" isEndLine: " + token.isEndLine());
		 */
		
		if (token.getType() == SVIndentTokenType.MultiLineComment) {
			SVMultiLineIndentToken mlc = (SVMultiLineIndentToken)token;
			token.setLeadingWS(fIndentStack.peek());
			for (int i=1; i<mlc.getCommentLines().size(); i++) {
				SVIndentToken t = mlc.getCommentLines().get(i);
				if (t.getImage().startsWith("*")) {
					t.setLeadingWS(fIndentStack.peek() + "  ");
				}
			}
		} else if (token.getType() == SVIndentTokenType.Operator && token.getImage().equals(";")) {
			// We've reached the end of a statement.
			// Determine how to indent this statement
			if (lineContains("class", token)) {
				fIndentStack.push(fIndentStack.peek() + "\t");
			}
			if (token.getType() == SVIndentTokenType.MultiLineComment) {
			} else {
				fFormatQueue.get(0).setLeadingWS(" ");
			}
			for (SVIndentToken t : fFormatQueue) {
				t.setDoIt(true);
			}
			fFormatQueue.clear();
		} else if (token.getType() == SVIndentTokenType.Identifier &&
				token.getImage().contains("end")) {
			if (token.getImage().equals("end") && token.isEndLine()) {
				if (fIndentStack.size() > 1) {
					fIndentStack.pop();
				}
			}
		} else if (token.getType() == SVIndentTokenType.Identifier &&
				token.getImage().equals("begin")) {
		} else {
			token.setDoIt(false);
			fFormatQueue.add(token);
		}
	}

	private boolean lineContains(String id, SVIndentToken tok) {
		int start = fFormatQueue.indexOf(tok);
		boolean ret = false;
		
		for (int i=start-1; i>=0; i--) {
			if (fFormatQueue.get(i).getImage().equals(id)) {
				ret = true;
			} else if (fFormatQueue.get(i).isStartLine()) {
				ret = false;
				break;
			}
		}
		
		return ret;
	}
	
	public void end() {
	}
	
}

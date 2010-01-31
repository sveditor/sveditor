package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.formatter.ContextBasedFormattingStrategy;
import org.eclipse.jface.text.formatter.IFormattingStrategy;

public class SVFormattingStrategy extends ContextBasedFormattingStrategy {

	@Override
	public void format() {
		super.format();
		System.out.println("format()");
	}

	@Override
	public String format(String content, boolean start, String indentation,
			int[] positions) {
		System.out.println("format: \"" + content + "\"; start=" + start + " indentation=\"" + indentation + "\"");
		return super.format(content, start, indentation, positions);
	}

	
}

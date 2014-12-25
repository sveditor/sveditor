package net.sf.sveditor.ui.text.hover;

public class SVHoverContentProvider {
	protected String				fContent;
	
	public SVHoverContentProvider(String content) {
		fContent = content;
	}

	public String getContent(SVHoverInformationControlInput input) {
		return fContent;
	}
	
}


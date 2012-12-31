package net.sf.sveditor.core.argfile.parser;

public class SVArgFileDefaultOptionProvider extends SVArgFileOptionProviderList {
	
	public SVArgFileDefaultOptionProvider() {
		add(new SVArgFileQuestaOptionProvider());
		add(new SVArgFileVCSOptionProvider());
		add(new SVArgFileNCVlogOptionProvider());
	}

}

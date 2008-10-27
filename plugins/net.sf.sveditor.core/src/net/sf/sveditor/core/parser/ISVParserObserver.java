package net.sf.sveditor.core.parser;

public interface ISVParserObserver {
	
	enum EventType {
		
	};
	
	void init(ISVParser parser);
	
	void parseEvent(EventType type, Object context);

}

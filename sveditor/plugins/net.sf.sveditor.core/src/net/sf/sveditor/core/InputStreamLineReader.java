package net.sf.sveditor.core;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

public class InputStreamLineReader extends Thread {
	private InputStream					fInput;
	private List<ILineListener>			fListeners;
	
	public InputStreamLineReader(
			InputStream				in,
			List<ILineListener> 	l) {
		fInput = in;
		fListeners = new ArrayList<ILineListener>(l);
	}

	@Override
	public void run() {
		try {
			InputStreamReader rdr = new InputStreamReader(fInput);
			BufferedReader brdr = new BufferedReader(rdr);
			String line;
			
			while ((line = brdr.readLine()) != null) {
				for (ILineListener l : fListeners) {
					synchronized (l) {
						l.line(line);
					}
				}
			}
		} catch (IOException e) {}
	}

}

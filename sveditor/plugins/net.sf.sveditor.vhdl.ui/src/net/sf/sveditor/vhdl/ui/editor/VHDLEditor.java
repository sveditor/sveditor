package net.sf.sveditor.vhdl.ui.editor;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Device;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.TextEditor;


public class VHDLEditor extends TextEditor {
	private Map<RGB, Color>			fColorCache;
	private Device					fDevice;
	private VHDLCodeScanner			fCodeScanner;

	public VHDLEditor() {
		fColorCache = new HashMap<RGB, Color>();
	}

	@Override
	public void createPartControl(Composite parent) {
		setSourceViewerConfiguration(new VHDLSourceViewerConfig(this));
		
		fDevice = parent.getShell().getDisplay();
		
		super.createPartControl(parent);
	}
	
	public VHDLCodeScanner getCodeScanner() {
		if (fCodeScanner == null) {
			fCodeScanner = new VHDLCodeScanner(this);
		}
		return fCodeScanner;
	}
	
	public Color getColor(RGB rgb) {
		if (fColorCache.containsKey(rgb)) {
			return fColorCache.get(rgb);
		} else {
			Color ret = new Color(fDevice, rgb);
			fColorCache.put(rgb, ret);
			
			return ret;
		}
	}

}

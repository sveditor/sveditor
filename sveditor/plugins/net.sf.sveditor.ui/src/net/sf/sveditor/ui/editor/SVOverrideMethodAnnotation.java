package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.text.source.Annotation;

public class SVOverrideMethodAnnotation extends Annotation {
	private SVDBTask			fTF;
	
	public SVOverrideMethodAnnotation(SVDBTask tf, String msg) {
		super(SVUiPlugin.PLUGIN_ID + ".methodOverride", false, msg);
		fTF = tf;
	}

	public SVDBTask getTask() {
		return fTF;
	}
}

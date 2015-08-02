package net.sf.sveditor.ui.wizards.project;

import net.sf.sveditor.core.Tuple;

public interface INewFilelistWizardPathValidator {

	// Tuple is: warning, error
	Tuple<String, String> isValid(String path);

}

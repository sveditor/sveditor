/*******************************************************************************
 * Copyright 2005-2007, CHISEL Group, University of Victoria, Victoria, BC,
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * 
 * Contributors: 
 * 		The Chisel Group, University of Victoria - initial contributor
 * 		Armond Paiva - repurposed for use in SVEditor
 * 
 ******************************************************************************/

package net.sf.sveditor.ui.views.diagram.figures;


import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.swt.graphics.Color;

public class UMLClassFigure extends Figure {
	
	public static Color classColor = null;

	private CompartmentFigure attributeFigure = new CompartmentFigure();
	private CompartmentFigure methodFigure = new CompartmentFigure();
	
//	private boolean fIsSelected = false ;

	public UMLClassFigure(Label name, boolean isSelected) {
		
		ToolbarLayout layout = new ToolbarLayout();
		setLayoutManager(layout);
		
		setBorder(new LineBorder(ColorConstants.black, 
				isSelected ? 5 : 1 ));
		
		if(UMLClassFigure.classColor == null) {
			UMLClassFigure.classColor = new Color(null, 255, 255, 206);		
		}
		
		setBackgroundColor(UMLClassFigure.classColor);
		setOpaque(true);

		add(name);
		add(attributeFigure);
		add(methodFigure);
	}
	
//	public void setSelected(boolean isSelected) {
//		fIsSelected = isSelected ;
//	}

	public CompartmentFigure getAttributesCompartment() {
		return attributeFigure;
	}

	public CompartmentFigure getMethodsCompartment() {
		return methodFigure;
	}
}
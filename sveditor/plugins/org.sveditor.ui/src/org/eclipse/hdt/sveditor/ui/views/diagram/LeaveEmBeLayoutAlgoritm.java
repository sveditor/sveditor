/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Armond Paiva - initial contributor
 ****************************************************************************/

package org.sveditor.ui.views.diagram;

import org.eclipse.zest.layouts.algorithms.AbstractLayoutAlgorithm;
import org.eclipse.zest.layouts.dataStructures.InternalNode;
import org.eclipse.zest.layouts.dataStructures.InternalRelationship;

//import org.eclipse.zest.layouts.interfaces.LayoutContext;
//
//
//public class LeaveEmBeLayoutAlgoritm implements LayoutAlgorithm {
//	
//	public LeaveEmBeLayoutAlgoritm(int styles) { }
//
//	public void setLayoutContext(LayoutContext context) { }
//
//	public void applyLayout(boolean clean) { }
//
//}




public class LeaveEmBeLayoutAlgoritm extends AbstractLayoutAlgorithm {
	
	public LeaveEmBeLayoutAlgoritm(int styles) { 
		super(styles) ;
	}

//	public void setLayoutContext(LayoutContext context) { }
//
//	public void applyLayout(boolean clean) { }

	@Override
	public void setLayoutArea(double x, double y, double width, double height) {
	}

	@Override
	protected boolean isValidConfiguration(boolean asynchronous, boolean continuous) {
		return true ;
	}

	@Override
	protected void applyLayoutInternal(InternalNode[] entitiesToLayout,
			InternalRelationship[] relationshipsToConsider, double boundsX,
			double boundsY, double boundsWidth, double boundsHeight) {
	}

	@Override
	protected void preLayoutAlgorithm(InternalNode[] entitiesToLayout,
			InternalRelationship[] relationshipsToConsider, double x, double y,
			double width, double height) {
	}
	

	@Override
	protected void postLayoutAlgorithm(InternalNode[] entitiesToLayout,
			InternalRelationship[] relationshipsToConsider) {
	}

	@Override
	protected int getTotalNumberOfLayoutSteps() {
		return 0;
	}

	@Override
	protected int getCurrentLayoutStep() {
		return 0;
	}

}
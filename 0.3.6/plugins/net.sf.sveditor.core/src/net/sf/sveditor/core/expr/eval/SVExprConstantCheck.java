/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.expr.eval;

import net.sf.sveditor.core.db.expr.SVCondExpr;
import net.sf.sveditor.core.db.expr.SVConstraintIfExpr;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.expr.SVExprIterator;
import net.sf.sveditor.core.db.expr.SVIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVImplicationExpr;
import net.sf.sveditor.core.db.expr.SVInsideExpr;

public class SVExprConstantCheck extends SVExprIterator {
	private IValueProvider			fValueProvider;
	private boolean					fIsConstant;
	
	public SVExprConstantCheck(IValueProvider provider) {
		fValueProvider = provider;
	}
	
	public synchronized boolean isConstant(SVExpr expr) {
		fIsConstant = true;
		
		visit(expr);
	
		return fIsConstant;
	}
	

	@Override
	protected void cond(SVCondExpr expr) {
		// TODO Auto-generated method stub
		super.cond(expr);
	}

	@Override
	protected void constraint_if(SVConstraintIfExpr expr) {
		fIsConstant = false;
		// TODO Auto-generated method stub
		super.constraint_if(expr);
	}

	@Override
	protected void implication(SVImplicationExpr expr) {
		// TODO Auto-generated method stub
		super.implication(expr);
	}

	@Override
	protected void inside(SVInsideExpr expr) {
		// Skip: visit(expr.getLhs());
		for (SVExpr e : expr.getValueRangeList()) {
			visit(e);
		}
	}

	@Override
	protected void identifier(SVIdentifierExpr expr) {
		try {
			fValueProvider.get_value(expr.getIdStr());
		} catch (Exception e) {
			fIsConstant = false;
		}
	}
}

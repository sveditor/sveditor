package net.sf.sveditor.core.expr.eval;

import java.math.BigInteger;

public interface IValueProvider {
	
	BigInteger get_value(String name) throws Exception;

}

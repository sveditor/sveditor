
cd scripts

%ECLIPSE_HOME%/eclipsec -nosplash -application org.eclipse.ant.core.antRunner --launcher.suppressErrors -buildfile mk_product.xml -Dos=win32 -Dws=win32 -Darch=x86 mk_product



rem cd scripts

rem %ECLIPSE_HOME%/eclipsec -nosplash -application org.eclipse.ant.core.antRunner --launcher.suppressErrors -buildfile mk_product.xml -Dos=win32 -Dws=win32 -Darch=x86 mk_product
%ECLIPSE_HOME%/eclipsec -nosplash -application org.eclipse.ant.core.antRunner --launcher.suppressErrors -buildfile mk_product.xml mk_product -Dos=win32


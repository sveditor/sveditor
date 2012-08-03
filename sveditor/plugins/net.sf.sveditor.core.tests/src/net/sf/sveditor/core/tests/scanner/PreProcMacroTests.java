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


package net.sf.sveditor.core.tests.scanner;

import java.io.InputStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.SVPreProcDirectiveScanner;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;

import org.apache.tools.ant.filters.StringInputStream;

public class PreProcMacroTests extends TestCase {
	
	public void testMultiTokenGlue() {
		LogHandle log = LogFactory.getLogHandle("testMultiTokenGlue");
		SVCorePlugin.getDefault().enableDebug(false);
		String text = 
			"`define analysis_closure_imp(data_type, target, func) \\\n" +
			"typedef class target; \\\n" +
			"class analysis_closure_``data_type``_``target``_``func \\\n" +
			"	extends ovm_component; \\\n" +
			"	ovm_analysis_imp #(data_type, \\\n" + 
			"		analysis_closure_``data_type``_``target``_``func) exp; \\\n" +
			"	\\\n" +
			"	target							m_target_ptr; \\\n" +
			"	\\\n" +
			"	function new(string name, target t); \\\n" +
			"		super.new(name, t); \\\n" +
			"		m_target_ptr = t; \\\n" +
			"		exp = new(\"exp\", this); \\\n" +
			"	endfunction \\\n" +
			"	\\\n" +
			"	virtual function void write(data_type t); \\\n" +
			"		m_target_ptr. func (t); \\\n" +
			"	endfunction \\\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"`analysis_closure_imp(foo, bar, write_func)\n" +
			"\n";
		String expected =
			"typedef class bar; \n" +
			"class analysis_closure_foo_bar_write_func \n" +
			"	extends ovm_component; \n" +
			"	ovm_analysis_imp #(foo, \n" +
			"		analysis_closure_foo_bar_write_func) exp; \n" +
			"	\n" +
			"	bar							m_target_ptr; \n" +
			"	\n" +
			"	function new(string name, bar t); \n" +
			"		super.new(name, t); \n" +
			"		m_target_ptr = t; \n" +
			"		exp = new(\"exp\", this); \n" +
			"	endfunction \n" +
			"	\n" +
			"	virtual function void write(foo t); \n" +
			"		m_target_ptr. write_func (t); \n" +
			"	endfunction \n" +
			"endclass";			
			
		InputStream in = new StringInputStream(text);
		SVPreProcDirectiveScanner sc = new SVPreProcDirectiveScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();

		sc.init(in, "text");
		sc.setObserver(ob);
		sc.process();

		SVDBFile pp_file = ob.getFiles().get(0);
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());

		SVDBFileTreeUtils	ft_utils = new SVDBFileTreeUtils();
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(null, null);
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider(mp);
		mp.setFileContext(ft_root);
		
		ft_utils.resolveConditionals(ft_root, dp);
		
		
		String result = dp.expandMacro("`analysis_closure_imp(foo, bar, write_func)", "text", 1);
		
		log.debug("expected: \"" + expected.trim() + "\"");
		log.debug("====");
		log.debug("result: \"" + result.trim() + "\"");
		assertEquals(expected, result.trim());
		
		LogFactory.removeLogHandle(log);
	}

	public void testNestedExpansion() {
		LogHandle log = LogFactory.getLogHandle("testNestedExpansion");
		String text = 
			"`define vmm_channel_( T ) T``_channel\n" +
			"\n" +
			"`define vmm_channel( T ) \\\n" +
			"class `vmm_channel_( T ) extends vmm_channel;";
		InputStream in = new StringInputStream(text);
		SVPreProcDirectiveScanner sc = new SVPreProcDirectiveScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();

		sc.init(in, "text");
		sc.setObserver(ob);
		sc.process();

		SVDBFile pp_file = ob.getFiles().get(0);
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());

		SVDBFileTreeUtils	ft_utils = new SVDBFileTreeUtils();
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(null, null);
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider(mp);
		mp.setFileContext(ft_root);
		
		ft_utils.resolveConditionals(ft_root, dp);
		
		
		String result = dp.expandMacro("`vmm_channel( foo )", "text", 1);
		
		log.debug("result: \"" + result + "\"");
		assertEquals("class  foo_channel extends vmm_channel;", result.trim());
		
		LogFactory.removeLogHandle(log);
	}
	
	public void testMacroContainingIfdef() {
		LogHandle log = LogFactory.getLogHandle("testMacroContainingIfdef");
		String content =
			"int MARKER=1;\n" +
			"`define macro \\\n" +
			"    `ifdef ENABLE_1\\\n" +
			"    int A1;\\\n" +
			"    `else\\\n" +
			"    int B1;\\\n" +
			"    `endif\n" +
			"\n" +
			"`define ENABLE_1\n" +
			"`macro\n" +
			"int MARKER_end=2;\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		InputStream in = new StringInputStream(content);
		SVPreProcDirectiveScanner pp_scanner = new SVPreProcDirectiveScanner();
		pp_scanner.init(in, "content");
		SVDBPreProcObserver observer = new SVDBPreProcObserver();
		pp_scanner.setObserver(observer);
		pp_scanner.process();
		
		SVDBFileTree ft = new SVDBFileTree(observer.getFiles().get(0));
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(null, null);
		mp.setFileContext(ft);
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);
		
		String out = dp.expandMacro("`macro", "content", 20);
		log.debug("Result:\n" + out);
		assertEquals("int A1;", out.trim());
		
		LogFactory.removeLogHandle(log);
	}
	
}

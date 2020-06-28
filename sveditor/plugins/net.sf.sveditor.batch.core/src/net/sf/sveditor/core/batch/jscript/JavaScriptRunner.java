/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.batch.jscript;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.List;

import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.Tuple;

import org.mozilla.javascript.Context;
import org.mozilla.javascript.NativeArray;
import org.mozilla.javascript.ScriptableObject;
import org.mozilla.javascript.tools.shell.Global;

public class JavaScriptRunner {
	
	private ILineListener			fOutLineListener = null;
	private ILineListener			fErrLineListener = null;
	
	public JavaScriptRunner() {
		
	}
	
	public void setOutLineListener(ILineListener l) {
		fOutLineListener = l;
	}
	
	public void setErrLineListener(ILineListener l) {
		fErrLineListener = l;
	}
	
	@SuppressWarnings("unchecked")
	public void run(
			Tuple<String, InputStream>		script,
			List<String>					arguments,
			File							working_dir) throws Exception {
		Tuple<String, InputStream> scripts[] = new Tuple[] {
				script
		};
		
		run(scripts, arguments, working_dir);
	}
	
	public void run(
			Tuple<String, InputStream>		scripts[],
			List<String>					arguments,
			File							working_dir) throws Exception {
		Context cx = Context.enter();

		
		PrintStream old_out = System.out;
		PrintStream old_err = System.err;
		String curr_wd = System.getProperty("user.dir");
		
		try {
			Global global = new Global(cx);
			
			// Set the command-line arguments
			NativeArray js_args = new NativeArray(arguments.toArray());
		
			ScriptableObject.putProperty(global, "arguments", js_args);
			
			if (fOutLineListener != null) {
				System.setOut(outStream);
			}
			
			if (fErrLineListener != null) {
				System.setErr(errStream);
			}
			
			if (working_dir != null) {
				System.setProperty("user.dir", working_dir.getAbsolutePath());
			}

			for (Tuple<String, InputStream> scr : scripts) {
				InputStreamReader reader = null;

				reader = new InputStreamReader(scr.second());

				try {
					cx.evaluateReader(global, reader, scr.first(), 1, null);
				} catch (IOException e) {
					throw new Exception("Failure during script \"" + 
							scr.first() + "\" execution\n" + e.getMessage());
				}
			}
		} finally {
			Context.exit();
			
			System.setOut(old_out);
			System.setErr(old_err);
			System.setProperty("user.dir", curr_wd);
			if (fErrLineListener != null) {
				errStream.flush();
			}
			if (fOutLineListener != null) {
				outStream.flush();
			}
		}
	}

	private PrintStream			errStream = new PrintStream(new ByteArrayOutputStream()) {
		
		StringBuilder			fOutput = new StringBuilder();
		

		@Override
		public void write(byte[] data, int off, int len) {
			for (int i=0; i<len; i++) {
				fOutput.append((char)data[off+i]);
				if (data[off+i] == '\n') {
					fErrLineListener.line(fOutput.toString());
					fOutput.setLength(0);
				}
			}
		}

		@Override
		public void write(int val) {
			fOutput.append((char)val);
			if (val == '\n') {
				fErrLineListener.line(fOutput.toString());
				fOutput.setLength(0);
			}
		}

		public void flush() {
			if (fOutput.length() > 0) {
				fErrLineListener.line(fOutput.toString());
				fOutput.setLength(0);
			}
			
		}		
	};
	
	private PrintStream			outStream = new PrintStream(new ByteArrayOutputStream()) {
		
		StringBuilder			fOutput = new StringBuilder();
		
		@Override
		public void write(byte[] data, int off, int len) {
			for (int i=0; i<len; i++) {
				fOutput.append((char)data[off+i]);
				if (data[off+i] == '\n') {
					fOutLineListener.line(fOutput.toString());
					fOutput.setLength(0);
				}
			}
		}

		@Override
		public void write(int val) {
			fOutput.append((char)val);
			if (val == '\n') {
				fOutLineListener.line(fOutput.toString());
				fOutput.setLength(0);
			}			
		}
		
		public void flush() {
			if (fOutput.length() > 0) {
				fOutLineListener.line(fOutput.toString());
				fOutput.setLength(0);
			}
			
		}
	};
}

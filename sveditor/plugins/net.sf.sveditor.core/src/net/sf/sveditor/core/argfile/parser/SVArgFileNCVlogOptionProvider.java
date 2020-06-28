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
package net.sf.sveditor.core.argfile.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVArgFileNCVlogOptionProvider implements ISVArgFileOptionProvider {
	
	private static final List<OptionInfo>		fOptionList;
	private LogHandle							fLog;
	private boolean							fDebugEn = true;
	
	private static class OptionInfo {
		private String				fOption;
		private String				fMinAbrev;
		private int				fArgs;
		
		public OptionInfo(String opt, int args) {
			
			int idx = 1;
			while (idx < opt.length() && 
					Character.isUpperCase(opt.charAt(idx))) {
				idx++;
			}
			if (idx > 0) {
				fMinAbrev = opt.substring(0, idx).toLowerCase();
			} else {
				fMinAbrev = null;
			}
			fOption = opt.toLowerCase();
			fArgs = args;
		}
		
		public String getName() {
			return fOption;
		}
		
		public int getArgCount() {
			return fArgs;
		}
		
		// this==target
		public boolean equals(Object obj) {
			if (obj instanceof OptionInfo) {
				OptionInfo other = (OptionInfo)obj;
				String opt = getName();
				opt = opt.toLowerCase();
				
				if (other.fMinAbrev != null) {
					boolean eq = true;
					int i;
					
					for (i=0; i<other.fMinAbrev.length() && i<opt.length(); i++) {
						if (other.fMinAbrev.charAt(i) != opt.charAt(i)) {
							eq = false;
							break;
						}
					}
					
					for (; i<other.fOption.length() && i<opt.length(); i++) {
						if (other.fOption.charAt(i) != opt.charAt(i)) {
							eq = false;
							break;
						}
					}
					
					return eq;
				} else {
					return other.fOption.equals(opt);
				}
			} else {
				return super.equals(obj);
			}
		}
	}
	
	static {
		fOptionList = new ArrayList<SVArgFileNCVlogOptionProvider.OptionInfo>();
		fOptionList.add(new OptionInfo("-64bit", 0));
		fOptionList.add(new OptionInfo("-AMs", 0));
		fOptionList.add(new OptionInfo("-APpend_log", 0));
		fOptionList.add(new OptionInfo("-ASsert", 0));
		fOptionList.add(new OptionInfo("-DEFine", 1));
		fOptionList.add(new OptionInfo("-File", 1));
		fOptionList.add(new OptionInfo("-INcdir", 1));
	}
	
	public SVArgFileNCVlogOptionProvider() {
		fLog = LogFactory.getLogHandle("SVArgFileNCVlogOptionProvider");
	}

	public List<String> getArgFilePaths(String option, String arg) {
		List<String> ret = new ArrayList<String>();
		ret.add(arg);
		return ret;
	}

	public OptionType getOptionType(String name) {
		int idx = fOptionList.indexOf(new OptionInfo(name, -1));
		if (fDebugEn) {
			fLog.debug("getOptionType: \"" + name + "\" => idx=" + idx);
		}
		if (idx >= 0) {
			String opt = fOptionList.get(idx).getName();
			if (opt.equals("-incdir")) {
				return OptionType.Incdir;
			} else if (opt.equals("-define")) {
				return OptionType.Define;
			} else if (opt.equals("-file")) {
				return OptionType.ArgFileInc;
			} else {
				return OptionType.Ignored;
			}
		} else {
			return OptionType.Unrecognized;
		}
	}

	public int optionArgCount(String name) {
		int idx = fOptionList.indexOf(new OptionInfo(name, -1));
		
		if (idx != -1) {
			OptionInfo info = fOptionList.get(idx);
			return info.getArgCount();
		} else {
			return 0;
		}
	}

	public List<String> getIncPaths(String option, String arg) {
		if (option.toLowerCase().startsWith("-in")) {
			List<String> ret = new ArrayList<String>();
			ret.add(arg);
			return ret;
		} else {
			return null;
		}
	}

	public Tuple<String, String> getDefValue(String option, String arg) {
		int idx = arg.indexOf('=');
		String key=null, val=null;
		
		if (idx >= 0) {
			key = arg.substring(0, idx);
			val = arg.substring(idx+1, arg.length());
		} else {
			key = arg;
		}
		
		Tuple<String, String> ret = new Tuple<String, String>(key, val);
	
		return ret;		
	}

}

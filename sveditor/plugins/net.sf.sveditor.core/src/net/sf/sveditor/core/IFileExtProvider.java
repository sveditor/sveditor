package net.sf.sveditor.core;

import java.util.Set;

public interface IFileExtProvider {
	
	Set<String> getSVRootFileExts();
	
	Set<String> getSVFileExts();

	Set<String> getVLRootFileExts();
	
	Set<String> getVLFileExts();


}

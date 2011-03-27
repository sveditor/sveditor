package net.sf.sveditor.core.tests;

import java.io.File;

import junit.framework.TestCase;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;
import net.sf.sveditor.core.db.index.cache.SVDBDirFS;
import net.sf.sveditor.core.db.index.cache.SVDBFileIndexCache;

public class TestIndexCacheFactory implements ISVDBIndexCacheFactory {
	private File				fRoot;
	
	public TestIndexCacheFactory(File dir) {
		fRoot = dir;
	}

	public ISVDBIndexCache createIndexCache(
			String project_name,
			String base_location) {
		if (fRoot == null) {
			return new TestNullIndexCache();
		} else {
			if (!fRoot.isDirectory()) {
				TestCase.assertTrue(fRoot.mkdirs());
			}
			String hash = SVFileUtils.computeMD5(base_location);
			File target = new File(fRoot, project_name + "_" + hash);
			System.out.println("Create index: " + target.getAbsolutePath());
			if (!target.isDirectory()) {
				TestCase.assertTrue(target.mkdirs());
			}
			
			SVDBFileIndexCache cache = new SVDBFileIndexCache(new SVDBDirFS(target));
			
			return cache;
		}
	}
	
	public static TestIndexCacheFactory instance(File dir) {
		return new TestIndexCacheFactory(dir);
	}
}

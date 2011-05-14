package net.sf.sveditor.core.db;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.attr.SVDBParentAttr;

@SuppressWarnings("rawtypes")
public class SVDBItemUtils {
	private static Map<SVDBItemType, Class>			fClassMap;


	public static synchronized ISVDBItemBase duplicate(ISVDBItemBase item) {
		ISVDBItemBase ret = null;
		if (fClassMap == null) {
			init();
		}
		
		if (item == null) {
			return null;
		}
		
		if (fClassMap.containsKey(item.getType())) {
			Class cls = fClassMap.get(item.getType());
			Object obj = null;
			try {
				obj = cls.newInstance();
			} catch (Exception e) {
				throw new RuntimeException("Failed to create object: " + 
						item.getType() + " " + e.getMessage());
			}

			ret = (ISVDBItemBase)obj;
		} else {
			throw new RuntimeException("Unsupported SVDBItemType " + item.getType());
		}
		
		duplicate(item.getClass(), ret, item);
		
		if (item instanceof ISVDBChildItem) {
			((ISVDBChildItem)ret).setParent(((ISVDBChildItem)item).getParent());
		}
		
		return ret;
	}
	
	private static void duplicate(Class cls, Object target, Object source) {
		if (cls.getSuperclass() != null && cls.getSuperclass() != Object.class) {
			duplicate(cls.getSuperclass(), target, source);
		}
		
		Field fields[] = cls.getDeclaredFields();
		
		for (Field f : fields) {
			f.setAccessible(true);
			
			if (!Modifier.isStatic(f.getModifiers())) {
				
				if (f.getAnnotation(SVDBParentAttr.class) != null ||
						f.getAnnotation(SVDBDoNotSaveAttr.class) != null) {
					try {
						f.set(target, f.get(source));
					} catch (IllegalAccessException e) {
						e.printStackTrace();
					}
					continue;
				}
				
				try {
					Class field_class = f.getType();
					
					if (Enum.class.isAssignableFrom(field_class)) {
						f.set(target, f.get(source));
					} else if (List.class.isAssignableFrom(field_class)) {
						Type t = f.getGenericType();
						if (t instanceof ParameterizedType) {
							ParameterizedType pt = (ParameterizedType)t;
							Type args[] = pt.getActualTypeArguments();
							if (args.length != 1) {
								throw new RuntimeException("" + args.length + "-parameter list unsupported");
							}
							Class c = (Class)args[0];
							if (c == String.class) {
								Object o = duplicateStringList(f.get(source));
								f.set(target, o);
							} else if (c == Integer.class) {
								f.set(target, duplicateIntList(f.get(source)));
							} else if (ISVDBItemBase.class.isAssignableFrom(c)) {
								if (target instanceof ISVDBChildItem) {
									f.set(target, duplicateItemList(f.get(source)));
								} else {
									f.set(target, duplicateItemList(f.get(source)));
								}
							} else {
								throw new RuntimeException("Type Arg: " + ((Class)args[0]).getName());
							}
						} else {
							throw new RuntimeException("Non-parameterized list");
						}
					} else if (Map.class.isAssignableFrom(field_class)) {
						Type t = f.getGenericType();
						if (t instanceof ParameterizedType) {
							ParameterizedType pt = (ParameterizedType)t;
							Type args[] = pt.getActualTypeArguments();
							Class key_c = (Class)args[0];
							Class val_c = (Class)args[1];
							if (key_c == String.class && val_c == String.class) {
								f.set(target, duplicateMapStringString(f.get(source)));
							} else {
								throw new RuntimeException("Map<" + key_c.getName() + ", " + val_c.getName() + ">: Class " + cls.getName());
							}
						} else {
							throw new RuntimeException("Non-parameterized list");
						}
					} else if (field_class == String.class) {
						f.set(target, f.get(source));
					} else if (field_class == int.class) {
						f.setInt(target, f.getInt(source));
					} else if (field_class == long.class) {
						f.setLong(target, f.getLong(source));
					} else if (field_class == boolean.class) {
						f.setBoolean(target, f.getBoolean(source));
					} else if (SVDBLocation.class == field_class) {
						f.set(target, duplicateSVDBLocation(f.get(source)));
					} else if (ISVDBItemBase.class.isAssignableFrom(field_class)) {
						f.set(target, duplicate((ISVDBItemBase)f.get(source)));
					} else {
						throw new RuntimeException("Unhandled class " + field_class.getName());
					}
				} catch (IllegalAccessException e) {
					e.printStackTrace();
					throw new RuntimeException("Generic Load Failure: " + e.getMessage());
				}
			}
		}
	}
	
	@SuppressWarnings({"unchecked"})
	private static Object duplicateStringList(Object src_obj) {
		List<String> ret = null;
		if (src_obj != null) {
			ret = new ArrayList<String>();
			List<String> src = (List<String>)src_obj;
			ret.addAll(src);
		}
		return ret;
	}
	
	@SuppressWarnings("unchecked")
	private static Object duplicateIntList(Object src_obj) {
		List<Integer> ret = null;
		if (src_obj != null) {
			ret = new ArrayList<Integer>();
			List<Integer> src = (List<Integer>)src_obj;
			ret.addAll(src);
		}
		return ret;
	}
	
	@SuppressWarnings("unchecked")
	private static Object duplicateItemList(Object src_obj) {
		List<ISVDBItemBase> ret = null;
		if (src_obj != null) {
			ret = new ArrayList<ISVDBItemBase>();
			List<ISVDBItemBase> src = (List<ISVDBItemBase>)src_obj;
			for (ISVDBItemBase it : src) {
				ret.add(duplicate(it));
			}
		}
		return ret;
	}
	
	@SuppressWarnings("unchecked")
	private static Object duplicateMapStringString(Object src_obj) {
		Map<String, String> ret = null;
		if (src_obj != null) {
			ret = new HashMap<String, String>();
			Map<String, String> src = (Map<String, String>)src_obj;
			for (Entry<String, String> e : src.entrySet()) {
				ret.put(e.getKey(), e.getValue());
			}
		}
		return ret;
	}
	
	private static Object duplicateSVDBLocation(Object src_obj) {
		SVDBLocation ret = null;
		if (src_obj != null) {
			SVDBLocation src = (SVDBLocation)src_obj;
			ret = new SVDBLocation(src);
		}
		return ret;
	}
	
	private static void init() {
		fClassMap 	= new HashMap<SVDBItemType, Class>();

		// Locate the class for each SVDBItemType element
		ClassLoader cl = SVDBItemUtils.class.getClassLoader();
		for (SVDBItemType v : SVDBItemType.values()) {
			String key = "SVDB" + v.name();
			Class cls = null;
			for (String pref : new String [] {"net.sf.sveditor.core.db.", 
					"net.sf.sveditor.core.db.stmt.",
			"net.sf.sveditor.core.db.expr."}) {
				try {
					cls = cl.loadClass(pref + key);
				} catch (Exception e) { }
			}

			if (cls == null) {
				System.out.println("Failed to locate class " + key);
			} else {
				fClassMap.put(v, cls);
			}
		}
	}
}

/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.persistence;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.net.URLClassLoader;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.attr.SVDBParentAttr;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class JITSVDBExprDelegateFactory implements Opcodes {
	private static JITSVDBExprDelegateFactory			fInstance;
	private Class<JITPersistenceDelegateBase>			fDelegateCls;
	private String										fTargetPkg;
	private String										fTargetPkgName;
	private Map<SVDBItemType, Class>					fTypeClassMap;
	private static final String							fBaseClass = "net/sf/sveditor/core/db/persistence/JITPersistenceDelegateBase";
	private static final String	fChildItem = "net/sf/sveditor/core/db/ISVDBChildItem";
	private static final String fDBFormatException = "net/sf/sveditor/core/db/persistence/DBFormatException";
	private static final String fDBWriteException = "net/sf/sveditor/core/db/persistence/DBWriteException";
	private boolean										fDebugEn;
	private int											fLevel;
	private static final int							READ_PARENT_PARAM 	= 1;
	private static final int							READ_OBJ_VAR 		= 2;
	
	private class JITClassLoader extends ClassLoader {
		private byte 									fClassBytes[];
		private Class<JITPersistenceDelegateBase>		fCls;
		
		
		JITClassLoader(ClassLoader parent, byte class_bytes[]) {
			super(parent);
			fClassBytes = class_bytes;
		}

		@Override
		protected Class<?> findClass(String name) throws ClassNotFoundException {
			if (name.equals(fTargetPkg + ".SVDBPersistenceDelegate")) {
				if (fCls == null) {
					fCls = (Class<JITPersistenceDelegateBase>)defineClass(
							name, fClassBytes, 0, fClassBytes.length);
				}
				return fCls;
			}
			
			return super.findClass(name);
		}
	}
	
	public JITSVDBExprDelegateFactory() {
		fTypeClassMap = new HashMap<SVDBItemType, Class>();
		fTargetPkg = "net.sf.sveditor.core.db.expr";
		fTargetPkgName = "net/sf/sveditor/core/db/expr";
	}
	
	private void build() {
		ClassWriter cw = new ClassWriter(0);
		final ClassLoader cl = getClass().getClassLoader();
		for (SVDBItemType t : SVDBItemType.values()) {
			Class cls = null;
			try {
				cls = cl.loadClass(fTargetPkg + ".SVDB" + t.name()); 
			} catch (Exception e) {}
			
			if (cls != null) {
				// Found a class to process
				fTypeClassMap.put(t, cls);
			}
		}
		
		long start = System.currentTimeMillis();
		build_boilerplate(cw);
		
		for (SVDBItemType t : fTypeClassMap.keySet()) {
			Class cls = fTypeClassMap.get(t);
			buildAccessors(cw, t, cls);
		}
		
		cw.visitEnd();
		
		JITClassLoader jit_cl = new JITClassLoader(cl, cw.toByteArray());
		try {
			fDelegateCls = (Class<JITPersistenceDelegateBase>)jit_cl.loadClass(
					fTargetPkg + ".SVDBPersistenceDelegate");
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		long end = System.currentTimeMillis();
		
		System.out.println("Class-build time: " + (end-start));
		System.out.println("Size: " + cw.toByteArray().length);
	}
	
	private void build_boilerplate(ClassWriter cw) {
		String classname = "SVDBPersistenceDelegate";
		cw.visit(Opcodes.V1_5, 
				ACC_PROTECTED+ACC_PUBLIC+ACC_SUPER,
				fTargetPkgName + "/" + classname,
				null,
				fBaseClass,
				null);
		cw.visitSource(classname + ".java", null);
				
		MethodVisitor mv;
		
		// Constructor
		mv = cw.visitMethod(ACC_PUBLIC, "<init>", "()V", null, null);
		mv.visitCode();
		mv.visitVarInsn(ALOAD, 0);
		mv.visitMethodInsn(INVOKESPECIAL, fBaseClass, "<init>", "()V");
		mv.visitInsn(RETURN);
		mv.visitMaxs(1, 1);
		mv.visitEnd();
	}
	
	private void buildAccessors(ClassWriter cw, SVDBItemType t, Class cls) {
		MethodVisitor mv;
		// Constructor
		String item_name = t.name();
		String tgt_clsname = cls.getName().replace('.', '/');
		
		// Read method
		//
		// 0 - this
		// 1 - parent
		// 2 - return
		mv = cw.visitMethod(ACC_PRIVATE, "read" + item_name, 
				"(L" + fChildItem + ";)L" + tgt_clsname + ";", 
				null, new String[] {fDBFormatException});
		mv.visitCode();
		mv.visitInsn(ACONST_NULL);
		mv.visitVarInsn(ASTORE, READ_OBJ_VAR); // Initialize return 
		visit(false, tgt_clsname, mv, cls);
		mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // Setup for return of var0
		mv.visitInsn(ARETURN);
		mv.visitMaxs(16, 16);
		mv.visitEnd();
		
		// Write method
		//
		// 0 - this
		// 1 - object
		mv = cw.visitMethod(ACC_PRIVATE, "write" + item_name, 
				"(L" + tgt_clsname + ";)V", 
				null, new String[] {fDBWriteException});
		mv.visitCode();
		visit(true, tgt_clsname, mv, cls);
		mv.visitInsn(RETURN);
		mv.visitMaxs(16, 16);
		mv.visitEnd();
	}
	
	protected void visit(
			boolean			write,
			String			target_classname,
			MethodVisitor	mv,
			Class 			cls) {
		if (fDebugEn) {
			debug("--> " + (++fLevel) + " accessObject: " + cls.getName());
		}
		
		if (cls.getSuperclass() != null && cls.getSuperclass() != Object.class) {
			String super_classname = transform_cls(cls.getSuperclass().getName());
			visit(write, super_classname, mv, cls.getSuperclass());
		}
		
		Field fields[] = cls.getDeclaredFields();
		
		for (Field f : fields) {
			f.setAccessible(true);
			if (Modifier.isStatic(f.getModifiers()) ||
				f.getAnnotation(SVDBDoNotSaveAttr.class) != null) {
				continue;
			}
			
			if (f.getAnnotation(SVDBParentAttr.class) != null) {
				if (!write) {
					// Load the object var onto the stack
					mv.visitVarInsn(ALOAD, READ_OBJ_VAR);
					// Load the parent var onto the stack
					mv.visitVarInsn(ALOAD, READ_PARENT_PARAM);
					mv.visitTypeInsn(CHECKCAST, fChildItem);
					mv.visitFieldInsn(PUTFIELD, 
							target_classname, 	// target classnae
							f.getName(), 		// field name
							// field type
							"L" + transform_cls(f.getClass().getName()) + ";");
				}
				continue;
			}

			try {
				Class field_class = f.getType();
				Object field_value = null;

				/**
				if (write) {
					field_value = f.get(target);
				}
				 */

				if (Enum.class.isAssignableFrom(field_class)) {
					if (fDebugEn) {
						debug("  " + fLevel + " Field " + f.getName() + " is an enum " + field_class.getName());
					}
					if (write) {
						// Load fParent field
						// 
						/*
						mv.visitFieldInsn(GETFIELD, owner, name, desc)
						mv.visitMethodInsn(INVOKEVIRTUAL, owner, name, desc)
						 */
					} else {
						
					}
					/** TODO: Invoke fParent.<rw>EnumType()
					if (write) {
						fParent.writeEnumType(field_class, (Enum)field_value);
					} else {
						f.set(target, fParent.readEnumType(field_class));
					}
					 */
				} else if (List.class.isAssignableFrom(field_class)) {
					Type t = f.getGenericType();
					if (t instanceof ParameterizedType) {
						ParameterizedType pt = (ParameterizedType)t;
						Type args[] = pt.getActualTypeArguments();
						if (args.length != 1) {
							throw new DBFormatException("" + args.length + "-parameter list unsupported");
						}
						Class c = (Class)args[0];
						if (c == String.class) {
							if (fDebugEn) {
								debug("  " + fLevel + " Field " + f.getName() + " is List<String>");
							}
							/** TODO: 
							if (write) {
								fParent.writeStringList((List<String>)field_value);
							} else {
								Object o = fParent.readStringList();
								f.set(target, o);
							}
							 */
						} else if (c == Integer.class) {
							if (fDebugEn) {
								debug("  " + fLevel + " Field " + f.getName() + " is List<Integer>");
							}
							/** TODO:
							if (write) {
								fParent.writeIntList((List<Integer>)field_value);
							} else {
								f.set(target, fParent.readIntList());
							}
							 */
						} else if (c == Long.class) {
							if (fDebugEn) {
								debug("  " + fLevel + " Field " + f.getName() + " is List<Long>");
							}
							/** TODO:
							if (write) {
								fParent.writeLongList((List<Long>)field_value);
							} else {
								f.set(target, fParent.readLongList());
							}
							 */
						} else if (ISVDBItemBase.class.isAssignableFrom(c)) {
							if (fDebugEn) {
								debug("  " + fLevel + " Field " + f.getName() + " is List<ISVDBItemBase>");
							}
							/** TODO:
							if (write) {
								fParent.writeItemList((List<ISVDBItemBase>)field_value);
							} else {
								if (target instanceof ISVDBChildItem) {
									f.set(target, fParent.readItemList((ISVDBChildItem)target));
								} else {
									f.set(target, fParent.readItemList(null));
								}
							}
							 */
						} else {
							if (fDebugEn) {
								debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is List<?>");
							}
							throw new DBFormatException("Type Arg: " + ((Class)args[0]).getName());
						}
					} else {
						if (fDebugEn) {
							debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unparameterized List");
						}
						throw new DBFormatException("Non-parameterized list");
					}
				} else if (Map.class.isAssignableFrom(field_class)) {
					Type t = f.getGenericType();
					if (t instanceof ParameterizedType) {
						ParameterizedType pt = (ParameterizedType)t;
						Type args[] = pt.getActualTypeArguments();
						Class key_c = null;
						Class val_c = null;

						if (args[0] instanceof Class) {
							key_c = (Class)args[0];
						} else {
							throw new DBFormatException("Failed to deconstruct type for " +
									"field " + f.getName()); 
						}

						if (args[1] instanceof Class) {
							val_c = (Class)args[0];
						} else if (args[1] instanceof ParameterizedType) {
							val_c = (Class)((ParameterizedType)args[1]).getRawType();
						} else {
							throw new DBFormatException("Failed to deconstruct type for " +
									"field " + f.getName()); 
						}
						if (key_c == String.class && val_c == String.class) {
							if (fDebugEn) {
								debug("  " + fLevel + " Field " + f.getName() + " is Map<String,String>");
							}
							/** TODO:
							if (write) {
								fParent.writeMapStringString((Map<String, String>)field_value);
							} else {
								f.set(target, fParent.readMapStringString());
							}
							 */
						} else if (key_c == String.class && val_c.isAssignableFrom(List.class)) {
							Class c = (Class)((ParameterizedType)args[1]).getActualTypeArguments()[0];
							if (fDebugEn) {
								debug("  " + fLevel + " Field " + f.getName() + " is Map<String,List>");
							}
							/** TODO:
							if (write) {
								fParent.writeMapStringList((Map<String,List>)field_value, c);
							} else {
								f.set(target, fParent.readMapStringList(c));
							}
							 */
						} else {
							if (fDebugEn) {
								debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unrecognized Map<?,?>");
							}
							throw new DBFormatException("Map<" + key_c.getName() + ", " + val_c.getName() + ">: Class " + cls.getName());
						}
					} else {
						if (fDebugEn) {
							debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unparameterized map");
						}
						throw new DBFormatException("Non-parameterized map");
					}
				} else if (field_class == String.class) {
					if (fDebugEn) {
						debug("  " + fLevel + " Field " + f.getName() + " is a String");
					}
					/** TODO:
					if (write) {
						fParent.writeString((String)field_value);
					} else {
						f.set(target, fParent.readString());
					}
					 */
				} else if (field_class == int.class) {
					if (fDebugEn) {
						debug("  " + fLevel + " Field " + f.getName() + " is an Integer");
					}
					/** TODO:
					if (write) {
						fParent.writeInt((Integer)field_value);
					} else {
						f.setInt(target, fParent.readInt());
					}
					 */
				} else if (field_class == long.class) {
					if (fDebugEn) {
						debug("  " + fLevel + " Field " + f.getName() + " is a Long");
					}
					/** TODO:
					if (write) {
						fParent.writeLong((Long)field_value);
					} else {
						f.setLong(target, fParent.readLong());
					}
					 */
				} else if (field_class == boolean.class) {
					if (fDebugEn) {
						debug("  " + fLevel + " Field " + f.getName() + " is a Boolean");
					}
					/** TODO:
					if (write) {
						fParent.writeBoolean((Boolean)field_value);
					} else {
						f.setBoolean(target, fParent.readBoolean());
					}
					 */
				} else if (SVDBLocation.class == field_class) {
					if (fDebugEn) {
						debug("  " + fLevel + " Field " + f.getName() + " is an SVDBLocation");
					}
					/** TODO:
					if (write) {
						fParent.writeSVDBLocation((SVDBLocation)field_value);
					} else {
						f.set(target, fParent.readSVDBLocation());
					}
					 */
				} else if (ISVDBItemBase.class.isAssignableFrom(field_class)) {
					if (fDebugEn) {
						debug("  " + fLevel + " Field " + f.getName() + " is an ISVDBItemBase");
					}
					/** TODO:
					if (write) {
						fParent.writeSVDBItem((ISVDBItemBase)field_value);
					} else {
						f.set(target, fParent.readSVDBItem(parent));
					}
					 */
				} else {
					if (fDebugEn) {
						debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unknown class type " + field_class.getName());
					}
					// throw new DBFormatException("Unhandled class " + field_class.getName());
				}
			} catch (/*IllegalAccess*/Exception e) {
				e.printStackTrace();
				// throw new DBFormatException("Generic Load Failure: " + e.getMessage());
			}
		}

		if (fDebugEn) {
			debug("<-- " + (fLevel--) + " accessObject: " + cls.getName());
		}
	}
	
	private static String transform_cls(String clsname) {
		return clsname.replace('.', '/');
	}
	
	public ISVDBPersistenceRWDelegate newDelegate() {
		try {
			JITPersistenceDelegateBase ret = fDelegateCls.newInstance();
			ret.init(fTypeClassMap.keySet());
			return ret;
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		} catch (InstantiationException e) {
			e.printStackTrace();
		}
		return null;
	}
	
	public static synchronized JITSVDBExprDelegateFactory instance() {
		if (fInstance == null) {
			fInstance = new JITSVDBExprDelegateFactory();
			fInstance.build();
		}
		return fInstance;
	}

	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}

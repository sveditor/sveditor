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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.attr.SVDBParentAttr;

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

public class JITSVDBExprDelegateFactory implements Opcodes {
	private static JITSVDBExprDelegateFactory			fInstance;
	private Class<JITPersistenceDelegateBase>			fDelegateCls;
	private String										fTargetPkg;
	private List<String>								fTargetPkgList;
	private Map<SVDBItemType, Class>					fTypeClassMap;
	private static final String							fBaseClass = "net/sf/sveditor/core/db/persistence/JITPersistenceDelegateBase";
	private static final String							fPersistenceDelegateParentClass = getClassName(ISVDBPersistenceRWDelegateParent.class);
	private static final String	fChildItem = "net/sf/sveditor/core/db/ISVDBChildItem";
	private static final String fDBFormatException = "net/sf/sveditor/core/db/persistence/DBFormatException";
	private static final String fDBWriteException = "net/sf/sveditor/core/db/persistence/DBWriteException";
	private static final String WRITE_ENUM_TYPE_SIG = "(Ljava/lang/Class;Ljava/lang/Enum;)V";
	private static final String READ_ENUM_TYPE_SIG = "(Ljava/lang/Class;)Ljava/lang/Enum;";
	private static final String WRITE_STRING_SIG   = "(Ljava/lang/String;)V";
	private static final String READ_STRING_SIG   = "()Ljava/lang/String;";
	private static final String WRITE_LOCATION_SIG   = "(Lnet/sf/sveditor/core/db/SVDBLocation;)V";
	private static final String READ_LOCATION_SIG   = "()Lnet/sf/sveditor/core/db/SVDBLocation;";
	private static final String READ_LIST_SIG       = "()Ljava/util/List;";
	private static final String WRITE_LIST_SIG      = "(Ljava/util/List;)V";
	private static final String READ_ITEM_LIST_SIG  = "(L" + fChildItem + ";)Ljava/util/List;";
	private static final String WRITE_INT_SIG = "(I)V";
	private static final String READ_INT_SIG = "()I";
	private static final String WRITE_LONG_SIG = "(J)V";
	private static final String READ_LONG_SIG = "()J";
	private static final String WRITE_BOOL_SIG = "(Z)V";
	private static final String READ_BOOL_SIG = "()Z";
	private static final String WRITE_ITEM_SIG = "(Lnet/sf/sveditor/core/db/ISVDBItemBase;)V";
	private static final String READ_ITEM_SIG = "()Lnet/sf/sveditor/core/db/ISVDBItemBase;";
	private static final String WRITE_MAP_SIG = "(Ljava/util/Map;)V";
	private static final String READ_MAP_SIG  = "()Ljava/util/Map;";
	private boolean										fDebugEn;
	private int											fLevel;
	private static final int							THIS_VAR			= 0;
	private static final int							READ_PARENT_VAR 	= 1;
	private static final int							READ_OBJ_VAR 		= 2;
	private static final int							WRITE_OBJ_VAR		= 1;
	private static String								fJitPersistenceBaseCls;
	private static String								fSVDBPersistenceRWDelegateParentCls;
	
	static {
		fJitPersistenceBaseCls = JITPersistenceDelegateBase.class.getName().replace('.', '/');
		fSVDBPersistenceRWDelegateParentCls = ISVDBPersistenceRWDelegateParent.class.getName().replace('.', '/');
	}
	
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
		fTargetPkg = "net.sf.sveditor.core.db";
		fTargetPkgList = new ArrayList<String>();
		fTargetPkgList.add("net.sf.sveditor.core.db");
		fTargetPkgList.add("net.sf.sveditor.core.db.expr");
		fTargetPkgList.add("net.sf.sveditor.core.db.stmt");
	}
	
	private void build() {
		ClassWriter cw = new ClassWriter(0);
		final ClassLoader cl = getClass().getClassLoader();
		for (SVDBItemType t : SVDBItemType.values()) {
			Class cls = null;
			for (String pkg : fTargetPkgList) {
				try {
					cls = cl.loadClass(pkg + ".SVDB" + t.name()); 
				} catch (Exception e) {}
				
				if (cls != null) {
					break;
				}
			}
			
			if (cls != null) {
				// Found a class to process
				fTypeClassMap.put(t, cls);
			} else {
				System.out.println("Error: Failed to find item " + t.name());
			}
		}
		
		long start = System.currentTimeMillis();
		build_boilerplate(cw);
		
		for (SVDBItemType t : fTypeClassMap.keySet()) {
//		for (SVDBItemType t : new SVDBItemType[] {SVDBItemType.Include}) {
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
		String full_classname = transform_cls(fTargetPkg) + "/" + classname;
		cw.visit(Opcodes.V1_5, 
				ACC_PROTECTED+ACC_PUBLIC+ACC_SUPER,
				full_classname,
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
		
		// writeItem Dispatch method
		mv = cw.visitMethod(ACC_PUBLIC, "writeSVDBItem",
				"(L" + getClassName(ISVDBItemBase.class) + ";)V",
				null, new String[] {fDBWriteException});
		// TODO: Just call writeInclude for now
		// TODO: call <obj>.getType()
		// call stack
		// object
		// this
		mv.visitVarInsn(ALOAD, THIS_VAR);
		mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
		mv.visitTypeInsn(CHECKCAST, getClassName(SVDBInclude.class));
		mv.visitMethodInsn(INVOKESPECIAL, full_classname, "writeInclude", 
				"(L" + getClassName(SVDBInclude.class) + ";)V");
		mv.visitInsn(RETURN);
		mv.visitMaxs(16, 16);
		mv.visitEnd();
		
		// readItem dispatch method
		mv = cw.visitMethod(ACC_PUBLIC, "readSVDBItem", 
				"(L" + getClassName(SVDBItemType.class) + ";L" + getClassName(ISVDBChildItem.class) + ";)L" + getClassName(ISVDBItemBase.class) + ";",
				null, new String[] {fDBWriteException});
		// TODO: Just call readInclude for now
		// call stack
		// parent object
		// this
		mv.visitVarInsn(ALOAD, THIS_VAR);
		mv.visitVarInsn(ALOAD, 2); // parent
		mv.visitMethodInsn(INVOKESPECIAL, full_classname, "readInclude", 
				"(L" + getClassName(ISVDBChildItem.class) + ";)L" + getClassName(SVDBInclude.class) + ";");
		mv.visitInsn(ARETURN);
		mv.visitMaxs(16, 16);
		mv.visitEnd();
	}
	
	/*
	private List readItemList(ISVDBChildItem parent) {
		return null;
	}
	
	protected ISVDBPersistenceRWDelegateParent		fParent; 

	private SVDBClassDecl readClassDecl(ISVDBChildItem parent) throws DBFormatException {
		SVDBClassDecl ret = new SVDBClassDecl();
		ret.fParams = readItemList(ret);

		fParent.readInt();
		
		return ret;
	}
	 */
	
	private void buildAccessors(ClassWriter cw, SVDBItemType t, Class cls) {
		MethodVisitor mv;
		
		if (fDebugEn) {debug("--> buildAccessor t=" + t.name() + " cls=" + cls.getName());}

		// Constructor
		String item_name = t.name();
		String tgt_clsname = getClassName(cls);
		
		// Read method
		//
		// 0 - this
		// 1 - parent
		// 2 - object
		mv = cw.visitMethod(ACC_PRIVATE, "read" + item_name, 
				"(L" + fChildItem + ";)L" + tgt_clsname + ";", 
				null, new String[] {fDBFormatException});
		mv.visitCode();
		mv.visitTypeInsn(NEW, tgt_clsname); // Create a new class instance
		mv.visitInsn(DUP);					// Duplicate handle. One will be consumed by the init call
		mv.visitMethodInsn(INVOKESPECIAL, tgt_clsname, "<init>", "()V");
//		mv.visitInsn(DUP);					// Duplicate. One will be consumed by store to obj-var
		mv.visitVarInsn(ASTORE, READ_OBJ_VAR); // Store handle to obj-var 
//		mv.visitVarInsn(ALOAD, THIS_VAR);
//		mv.visitVarInsn(ALOAD, READ_OBJ_VAR);
//		mv.visitMethodInsn(INVOKESPECIAL, tgt_clsname, "<init>", "()V");
//		mv.visit
//		mv.visitInsn(ACONST_NULL);
//		mv.visitVarInsn(ASTORE, READ_OBJ_VAR); // Initialize return 
		visit(false, tgt_clsname, mv, cls);
		mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // Setup for return of var0
		mv.visitInsn(ARETURN);
		mv.visitMaxs(3, 3);
		mv.visitEnd();
		
		// Write method
		//
		// 0 - this
		// 1 - object
		mv = cw.visitMethod(ACC_PRIVATE, "write" + item_name, 
				// "(L" + tgt_clsname + ";)V",
				"(L" + tgt_clsname + ";)V",
				null, new String[] {fDBWriteException});
		mv.visitCode();
		visit(true, tgt_clsname, mv, cls);
		mv.visitInsn(RETURN);
		mv.visitMaxs(3, 3);
		mv.visitEnd();
		
		if (fDebugEn) {debug("<-- buildAccessor t=" + t + " cls=" + cls.getName());}
	}
	
	protected void visit(
			boolean			write,
			String			tgt_classname,
			MethodVisitor	mv,
			Class 			cls) {
		if (fDebugEn) {
			debug("--> " + (++fLevel) + " accessObject: " + cls.getName());
		}
		
		if (cls.getSuperclass() != null && cls.getSuperclass() != Object.class) {
			String tgt_super_classname = getClassName(cls.getSuperclass());
			visit(write, tgt_super_classname, mv, cls.getSuperclass());
		}
		
		Field fields[] = cls.getDeclaredFields();
		
		for (Field f : fields) {
			// f.setAccessible(true);
			Class field_class = f.getType();
			String field_classname = getClassName(field_class);
			
			if (!Modifier.isStatic(f.getModifiers())) {
				
				if (f.getAnnotation(SVDBParentAttr.class) != null) {
					if (!write) {
						// PUTFIELD Requires:
						// target value [0]
						// target object [1]
						mv.visitVarInsn(ALOAD, READ_OBJ_VAR);
						mv.visitVarInsn(ALOAD, READ_PARENT_VAR);
						mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
								"L" + field_classname + ";");
					}
					continue;
				}
				
				if (f.getAnnotation(SVDBDoNotSaveAttr.class) != null) {
					continue;
				}
				
				try {
					Object field_value = null;
				
					if (Enum.class.isAssignableFrom(field_class)) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an enum " + field_class.getName());
						}
						if (write) {
							// Load up the field value and call writeEnumType
							// Desired stack layout is:
							// enum value
							// enum class
							// fParent
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Load target class name
							mv.visitLdcInsn(org.objectweb.asm.Type.getType(field_class));
							
							// Load field value
							mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
							mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"writeEnumType", WRITE_ENUM_TYPE_SIG);
						} else {
							// Invoke the parent to read the enum value
							// Store the result back to the field
							mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // for later use
							
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Stack layout must be:
							// enum class
							// fParent
							
							// Load target class name
							mv.visitLdcInsn(org.objectweb.asm.Type.getType(field_class));
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"readEnumType", READ_ENUM_TYPE_SIG);
							
							// Now, store the result back to the target field
							// Desired layout
							// enum value -- from calling readEnumType
							// object handle -- loaded at beginning
							System.out.println("Field " + f.getName() + " has type " + field_classname);
							mv.visitTypeInsn(CHECKCAST, field_classname);
							mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
							/*
							mv.visitVarInsn(ASTORE, READ_OBJ_VAR);
							 */
						}
					} else if (List.class.isAssignableFrom(field_class)) {
						Type t = f.getGenericType();
						if (t instanceof ParameterizedType) {
							ParameterizedType pt = (ParameterizedType)t;
							Type args[] = pt.getActualTypeArguments();
							String readMethod=null, writeMethod=null;
							boolean useStdRW = true;
							if (args.length != 1) {
								throw new DBFormatException("" + args.length + "-parameter list unsupported");
							}
							Class c = (Class)args[0];
							if (c == String.class) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<String>");
								}
								writeMethod = "writeStringList";
								readMethod = "readStringList";
							} else if (c == Integer.class) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<Integer>");
								}
								writeMethod = "writeIntList";
								readMethod  = "readIntList";
							} else if (c == Long.class) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<Long>");
								}
								writeMethod = "writeLongList";
								readMethod  = "readLongList";
							} else if (ISVDBItemBase.class.isAssignableFrom(c)) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is List<ISVDBItemBase>");
								}
								writeMethod = "writeItemList";
								
								if (!write) {
									useStdRW = false;
									// Invoke the parent to read the enum value
									// Store the result back to the field
									mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // for later use

									mv.visitVarInsn(ALOAD, THIS_VAR); 
									mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
											"L" + fPersistenceDelegateParentClass + ";");
									// fParent handle left on the stack

									// Stack layout must be:
									// enum class
									// fParent

									mv.visitVarInsn(ALOAD, READ_PARENT_VAR);
									mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
											"readItemList", READ_ITEM_LIST_SIG);

									// Now, store the result back to the target field
									// Desired layout
									// enum value -- from calling readEnumType
									// object handle -- loaded at beginning
									mv.visitTypeInsn(CHECKCAST, field_classname);
									mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
											"L" + field_classname + ";");
								}
							} else {
								if (fDebugEn) {
									debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is List<?>");
								}
								throw new DBFormatException("Type Arg: " + ((Class)args[0]).getName());
							}
							if (useStdRW) {
								if (write) {
									// Load up the field value and call writeStringList
									// Desired stack layout is:
									// enum value
									// enum class
									// fParent
									mv.visitVarInsn(ALOAD, THIS_VAR); 
									mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
											"L" + fPersistenceDelegateParentClass + ";");
									// fParent handle left on the stack

									// Load field value
									mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
									mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), 
											"L" + field_classname + ";");
									mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
											writeMethod, WRITE_LIST_SIG);
								} else {
									// Invoke the parent to read the enum value
									// Store the result back to the field
									mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // for later use

									mv.visitVarInsn(ALOAD, THIS_VAR); 
									mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
											"L" + fPersistenceDelegateParentClass + ";");
									// fParent handle left on the stack

									// Stack layout must be:
									// enum class
									// fParent

									mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
											readMethod, READ_LIST_SIG);

									// Now, store the result back to the target field
									// Desired layout
									// enum value -- from calling readEnumType
									// object handle -- loaded at beginning
									mv.visitTypeInsn(CHECKCAST, field_classname);
									mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
											"L" + field_classname + ";");
								}
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
							String readMethod=null, writeMethod=null;
							
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
								writeMethod = "writeMapStringString";
								readMethod  = "readMapStringString";
							} else if (key_c == String.class && val_c.isAssignableFrom(List.class)) {
								if (fDebugEn) {
									debug("  " + fLevel + " Field " + f.getName() + " is Map<String,List>");
								}
								writeMethod = "writeMapStringList";
								readMethod  = "readMapStringList";
							} else {
								if (fDebugEn) {
									debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unrecognized Map<?,?>");
								}
								throw new DBFormatException("Map<" + key_c.getName() + ", " + val_c.getName() + ">: Class " + cls.getName());
							}
							if (write) {
								// Load up the field value and call writeStringList
								// Desired stack layout is:
								// enum value
								// enum class
								// fParent
								mv.visitVarInsn(ALOAD, THIS_VAR); 
								mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
										"L" + fPersistenceDelegateParentClass + ";");
								// fParent handle left on the stack

								// Load field value
								mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
								mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), 
										"L" + field_classname + ";");
								mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
										writeMethod, WRITE_MAP_SIG);
							} else {
								// Invoke the parent to read the enum value
								// Store the result back to the field
								mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // for later use

								mv.visitVarInsn(ALOAD, THIS_VAR); 
								mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
										"L" + fPersistenceDelegateParentClass + ";");
								// fParent handle left on the stack

								// Stack layout must be:
								// enum class
								// fParent

								mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
										readMethod, READ_MAP_SIG);

								// Now, store the result back to the target field
								// Desired layout
								// enum value -- from calling readEnumType
								// object handle -- loaded at beginning
								mv.visitTypeInsn(CHECKCAST, field_classname);
								mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
										"L" + field_classname + ";");
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
						if (write) {
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
							mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
							// field value left on stack
							
							// Call writeString
							// Stack layout:
							// field value
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"writeString", WRITE_STRING_SIG);
						} else {
							mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // used by final PUTFIELD
							
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Call readString
							// Stack layout:
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"readString", READ_STRING_SIG);
							
							// stack
							// object -- result of readString
							// object var
							mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
						}
					} else if (field_class == int.class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an Integer");
						}
						if (write) {
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
							mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), "I"); 
							// field value left on stack
							
							// Call writeString
							// Stack layout:
							// field value
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"writeInt", WRITE_INT_SIG);
						} else {
							mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // used by final PUTFIELD
							
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Call readString
							// Stack layout:
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"readInt", READ_INT_SIG);
							mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), "I");
						}
					} else if (field_class == long.class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is a Long");
						}
						if (write) {
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
							mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), "J"); 
							// field value left on stack
							
							// Call writeString
							// Stack layout:
							// field value
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"writeInt", WRITE_LONG_SIG);
						} else {
							mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // used by final PUTFIELD
							
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Call readString
							// Stack layout:
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"readInt", READ_LONG_SIG);
							mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), "J"); 
						}
					} else if (field_class == boolean.class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is a Boolean");
						}
						if (write) {
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
							mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), "Z"); 
							// field value left on stack
							
							// Call writeString
							// Stack layout:
							// field value
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"writeInt", WRITE_BOOL_SIG);
						} else {
							mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // used by final PUTFIELD
							
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Call readString
							// Stack layout:
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"readInt", READ_BOOL_SIG);
							mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), "Z"); 
						}
					} else if (SVDBLocation.class == field_class) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an SVDBLocation");
						}
						if (write) {
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
							mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
							// field value left on stack
							
							// Call writeString
							// Stack layout:
							// field value
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"writeSVDBLocation", WRITE_LOCATION_SIG);
						} else {
							mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // used by final PUTFIELD
							
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Call readString
							// Stack layout:
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"readSVDBLocation", READ_LOCATION_SIG);
							mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
						}
					} else if (ISVDBItemBase.class.isAssignableFrom(field_class)) {
						if (fDebugEn) {
							debug("  " + fLevel + " Field " + f.getName() + " is an ISVDBItemBase");
						}
						if (write) {
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							mv.visitVarInsn(ALOAD, WRITE_OBJ_VAR);
							mv.visitFieldInsn(GETFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
							// field value left on stack
							
							// Call writeString
							// Stack layout:
							// field value
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"writeSVDBItem", WRITE_ITEM_SIG);
						} else {
							mv.visitVarInsn(ALOAD, READ_OBJ_VAR); // used by final PUTFIELD
							
							// Load the parent handle
							mv.visitVarInsn(ALOAD, THIS_VAR); 
							mv.visitFieldInsn(GETFIELD, fBaseClass, "fParent", 
									"L" + fPersistenceDelegateParentClass + ";");
							// fParent handle left on the stack
							
							// Call readString
							// Stack layout:
							// parent handle
							mv.visitMethodInsn(INVOKEINTERFACE, fPersistenceDelegateParentClass, 
									"readSVDBItem", READ_ITEM_SIG);
							mv.visitTypeInsn(CHECKCAST, field_classname);
							mv.visitFieldInsn(PUTFIELD, tgt_classname, f.getName(), 
									"L" + field_classname + ";");
						}
					} else {
						if (fDebugEn) {
							debug("  " + fLevel + " [ERROR] Field " + f.getName() + " is an unknown class type " + field_class.getName());
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
//					throw new DBFormatException("Generic Load Failure: " + e.getMessage());
				}
			}
		}

		if (fDebugEn) {
			debug("<-- " + (fLevel--) + " accessObject: " + cls.getName());
		}
	}
	
	private static String getClassName(Class cls) {
		return transform_cls(cls.getName());
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

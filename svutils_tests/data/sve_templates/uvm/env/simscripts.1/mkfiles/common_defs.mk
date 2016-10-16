
# Determine the platform
COMMON_DEFS_MK := $(lastword $(MAKEFILE_LIST))
COMMON_DEFS_MK_DIR := $(dir $(COMMON_DEFS_MK))

include $(COMMON_DEFS_MK_DIR)/plusargs.mk

OS=$(shell uname -o)
ARCH=$(shell uname -m)

ifeq (Cygwin,$(OS))
  DYNLINK=false
  DLLEXT=.dll
  ifeq ($(ARCH), x86_64)
    PLATFORM=cygwin64
  else
    PLATFORM=cygwin
  endif
else # Linux
ifeq (Linux,$(shell uname))
  DLLEXT=.so
  LIBPREF=lib
  DYNLINK=true
  ifeq ($(ARCH), x86_64)
    PLATFORM=linux_x86_64
  else
    PLATFORM=linux
  endif
else
  PLATFORM=unknown
  DYNLINK=unknown
endif
endif


ifeq (Cygwin,$(OS))
  ifeq ($(ARCH),x86_64)
    SYSTEMC_LIBDIR=$(SYSTEMC)/lib-cygwin64
  else
    SYSTEMC_LIBDIR=$(SYSTEMC)/lib-cygwin
  endif
  SYSTEMC_LIB=$(SYSTEMC_LIBDIR)/libsystemc.a
  LINK_SYSTEMC=$(SYSTEMC_LIBDIR)/libsystemc.a
endif

ifeq (,$(A23_CXX))
A23_CXX=arm-none-eabi-g++
endif
ifeq (,$(A23_AR))
A23_AR=arm-none-eabi-ar
endif

LINK=$(CXX)
DLLOUT=-shared

# CXXFLAGS += -I$(SYSTEMC)/include
ifneq (Cygwin,$(OS))
CXXFLAGS += -fPIC
CFLAGS += -fPIC
else
CXXFLAGS += -Wno-attributes
endif

CXXFLAGS += -g
CXXFLAGS += -I$(VERILATOR_ROOT)/include
CXXFLAGS += -I$(VERILATOR_ROOT)/include/vltstd
CXXFLAGS += -std=c++0x

# VERBOSE=true

ifneq (true,$(VERBOSE))
Q=@
endif


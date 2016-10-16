
#********************************************************************
#* Compile rules
#********************************************************************
# LIB_TARGETS += $(BUILD_DIR)/libs/tb_dpi.so

#LD_LIBRARY_PATH := $(SVF_LIBDIR)/dpi:$(LD_LIBRARY_PATH)
#export LD_LIBRARY_PATH
#CXXFLAGS += -I$(QUESTA_HOME)/include -I$(QUESTA_HOME)/include/systemc


ifeq (,$(QUESTA_HOME))
QUESTA_HOME := $(dir $(shell which vsim))
QUESTA_HOME := $(shell dirname $(QUESTA_HOME))
endif

ifeq (Cygwin,$(OS))
# Ensure we're using a Windows-style path for QUESTA_HOME
QUESTA_HOME:= $(shell cygpath -w $(QUESTA_HOME))

DPI_LIB := -Bsymbolic -L $(QUESTA_HOME)/win64 -lmtipli
endif

# Auto-identify GCC installation
ifeq ($(OS),Cygwin)
GCC_VERSION := 4.5.0

ifeq ($(ARCH),x86_64)
GCC_INSTALL := $(QUESTA_HOME)/gcc-$(GCC_VERSION)-mingw64vc12
LD:=$(GCC_INSTALL)/libexec/gcc/$(ARCH)-w64-mingw32/$(GCC_VERSION)/ld
else
GCC_INSTALL := $(QUESTA_HOME)/gcc-$(GCC_VERSION)-mingw32vc12
LD:=$(GCC_INSTALL)/libexec/gcc/$(ARCH)-w32-mingw32/$(GCC_VERSION)/ld
endif

else # Not Cygwin
ifeq (,$(wildcard $(QUESTA_HOME)/gcc-4.7.4-linux-*))
GCC_VERSION := 4.7.4
else
GCC_VERSION := 4.5.0
endif

ifeq ($(ARCH),x86_64)
GCC_INSTALL := $(QUESTA_HOME)/gcc-$(GCC_VERSION)-linux_x86_64
else
GCC_INSTALL := $(QUESTA_HOME)/gcc-$(GCC_VERSION)-linux
endif

endif
CC:=$(GCC_INSTALL)/bin/gcc
CXX:=$(GCC_INSTALL)/bin/g++

ifeq ($(DEBUG),true)
	TOP=$(TOP_MODULE)_dbg
	DOFILE_COMMANDS += "log -r /\*;"
else
	TOP=$(TOP_MODULE)_opt
endif

ifeq (true,$(DYNLINK))
define MK_DPI
	$(LINK) $(DLLOUT) -o $@ $^ $(DPI_LIB)
endef
else
define MK_DPI
	rm -f $@
	$(LD) -r -o $@ $^ 
#	$(AR) vcq $@ $^ 
endef
endif

VSIM_FLAGS += -batch

ifeq (true,$(QUIET))
VSIM_FLAGS += -nostdout
REDIRECT:= >/dev/null 2>&1
else
endif

build : vlog_build $(LIB_TARGETS) $(TESTBENCH_OBJS) target_build

.phony: vopt vopt_opt vopt_dbg vopt_compile
vlog_build : vopt

vopt : vopt_opt vopt_dbg

vopt_opt : vopt_compile
	$(Q)vopt -o $(TB)_opt $(TB) +cover $(REDIRECT)

vopt_dbg : vopt_compile
	$(Q)vopt +acc -o $(TB)_dbg $(TB) +cover $(REDIRECT)

vopt_compile :
	$(Q)rm -rf work
	$(Q)vlib work
	$(Q)vlog -sv \
		$(QS_VLOG_ARGS) \
		$(VLOG_ARGS)

#$(BUILD_DIR)/libs/tb_dpi.so : $(TESTBENCH_OBJS) $(BFM_LIBS) $(LIBSVF)
#	if test ! -d $(BUILD_DIR)/libs; then mkdir -p $(BUILD_DIR)/libs; fi
#	$(CXX) -o $@ -shared $(filter %.o, $^) \
#		$(foreach l,$(filter %.so, $^), -L$(dir $(l)) -l$(subst lib,,$(basename $(notdir $(l))))) \
#		$(LIBSVF_LINK)
		
#********************************************************************
#* Simulation settings
#********************************************************************
#ifeq ($(DEBUG),true)
#	TOP:=$(TOP_MODULE)_dbg
#	DOFILE_COMMANDS += "log -r /*;"
#else
#	TOP:=$(TOP_MODULE)_opt
#endif
#	vsim -c -do run.do $(TOP) -qwavedb=+signal \

ifeq (true,$(DYNLINK))
DPI_LIB_OPTIONS := $(foreach dpi,$(DPI_LIBRARIES),-sv_lib $(dpi))
else
# DPI_LIB_OPTIONS := $(foreach dpi,$(DPI_LIBRARIES),-dpilib $(dpi)$(DPIEXT))
DPI_LIB_OPTIONS := $(foreach dpi,$(DPI_LIBRARIES),-ldflags $(dpi)$(DPIEXT))
endif


run :
	$(Q)echo $(DOFILE_COMMANDS) > run.do
	$(Q)echo "coverage save -onexit cov.ucdb" >> run.do
	$(Q)echo "run $(TIMEOUT); quit -f" >> run.do
	$(Q)vmap work $(BUILD_DIR)/work $(REDIRECT)
#	$(Q)vsim $(VSIM_FLAGS) -batch -do run.do $(TOP) -coverage -l simx.log \
#		+TESTNAME=$(TESTNAME) -f sim.f $(DPI_LIB_OPTIONS) $(REDIRECT)
	$(Q)vsim $(VSIM_FLAGS) -do run.do $(TOP) -coverage -l simx.log \
		+TESTNAME=$(TESTNAME) -f sim.f $(DPI_LIB_OPTIONS) $(REDIRECT)


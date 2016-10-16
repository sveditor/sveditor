
TOP_MODULE ?= $(TB)
DEBUG ?= false
TIMEOUT ?= 1ms

COMMON_SIM_MK := $(lastword $(MAKEFILE_LIST))
COMMON_SIM_MK_DIR := $(dir $(COMMON_SIM_MK))
export COMMON_SIM_MK_DIR


DLLEXT=.so
LIBPREF=lib
SVF_LIBDIR ?= $(BUILD_DIR)/libs
SVF_OBJDIR ?= $(BUILD_DIR)/objs

ifeq (,$(DEFAULT_SIM))
SIM:=qs
else
SIM:=$(DEFAULT_SIM)
endif

include $(COMMON_SIM_MK_DIR)/common_defs.mk
include $(MK_INCLUDES)

ifeq (true,$(DYNLINK))
DPIEXT=.so
else
DPIEXT=.o
endif

#ifeq (Cygwin,$(OS))
#BUILD_DIR := $(shell cygpath -w $(BUILD_DIR))
#SIM_DIR := $(shell cygpath -w $(SIM_DIR))
#endif

CXXFLAGS += $(foreach dir, $(SRC_DIRS), -I$(dir))

vpath %.cpp $(SRC_DIRS)
vpath %.S $(SRC_DIRS)
vpath %.c $(SRC_DIRS)

.phony: all build run target_build

all :
	echo "Error: Specify target of build or run
	exit 1

include $(COMMON_SIM_MK_DIR)/sim_mk/common_sim_$(SIM).mk	

target_build :
	echo "SIM=$(SIM)"
	if test "x$(TARGET_MAKEFILE)" != "x"; then \
		$(MAKE) -f $(TARGET_MAKEFILE) build; \
	fi

ifeq (,$(wildcard $(SIM_DIR)/scripts/vlog_$(SIM).f))
#ifeq (Cygwin,$(OS))
#VLOG_ARGS += -f $(shell cygpath -w $(SIM_DIR)/scripts/vlog.f)
#else
VLOG_ARGS += -f $(SIM_DIR)/scripts/vlog.f
#endif
else
#ifeq (Cygwin,$(OS))
#VLOG_ARGS += -f $(shell cygpath -w $(SIM_DIR)/scripts/vlog_$(SIM).f)
#else
VLOG_ARGS += -f $(SIM_DIR)/scripts/vlog_$(SIM).f
#endif
endif


LD_LIBRARY_PATH := $(BUILD_DIR)/libs:$(LD_LIBRARY_PATH)

LD_LIBRARY_PATH := $(foreach path,$(BFM_LIBS),$(dir $(path)):)$(LD_LIBRARY_PATH)
export LD_LIBRARY_PATH

RULES := 1
include $(COMMON_SIM_MK_DIR)/common_rules.mk
include $(MK_INCLUDES)

ifeq (true,$(VERBOSE))
$(SVF_OBJDIR)/%.o : %.cpp
	if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(CXX) -c -o $@ $(CXXFLAGS) $^
	
$(SVF_LIBDIR)/%.a : 
	if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	rm -f $@
	ar vcq $@ $^
	
$(SVF_LIBDIR)/sc/%.so : 
	if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(LINK) -shared -o $@ $^
	
$(SVF_LIBDIR)/dpi/%.so : 
	if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(LINK) -shared -o $@ $^
	
$(SVF_LIBDIR)/sc_qs/%.so : 
	if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(LINK) -shared -o $@ $^
else
$(SVF_OBJDIR)/%.o : %.cpp
	@if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	@echo "$(CXX) `basename $^`"
	@$(CXX) -c -o $@ $(CXXFLAGS) $^
	
$(SVF_LIBDIR)/%.a : 
	@if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	@rm -f $@
	@echo "ar `basename $@`"
	@ar vcq $@ $^ > /dev/null 2>&1
	
$(SVF_LIBDIR)/sc/%.so : 
	@if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	@echo "link `basename $@`"
	@$(LINK) -shared -o $@ $^
	
$(SVF_LIBDIR)/dpi/%.so : 
	@if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	@echo "link `basename $@`"
	@$(LINK) -shared -o $@ $^
	
$(SVF_LIBDIR)/sc_qs/%.so : 
	@if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	@echo "link `basename $@`"
	@$(LINK) -shared -o $@ $^
	
endif	

	

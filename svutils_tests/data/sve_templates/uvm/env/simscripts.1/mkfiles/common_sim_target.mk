
COMMON_SIM_TARGET_MK := $(lastword $(MAKEFILE_LIST))
COMMON_SIM_TARGET_MK_DIR := $(dir $(COMMON_SIM_TARGET_MK))

include $(COMMON_SIM_TARGET_MK_DIR)/plusargs.mk


# include $(COMMON_SIM_MK_DIR)/common_defs.mk
include $(COMMON_SIM_TARGET_MK_DIR)/esw_mk/common_esw_$(TARGET).mk
include $(MK_INCLUDES)

CXXFLAGS += $(foreach dir, $(SRC_DIRS), -I$(dir))

LIB_TARGETS += $(BFM_LIBS)

vpath %.cpp $(SRC_DIRS)
vpath %.S $(SRC_DIRS)
vpath %.c $(SRC_DIRS)

.phony: all build 

all :
	echo "Error: Specify target of build or run
	exit 1

build : $(LIB_TARGETS) $(EXE_TARGETS)
	echo "EXE_TARGETS: $(EXE_TARGETS)"


RULES := 1
# include $(COMMON_SIM_MK_DIR)/common_rules.mk
include $(COMMON_SIM_TARGET_MK_DIR)/esw_mk/common_esw_$(TARGET).mk
include $(MK_INCLUDES)

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

%.o : %.cpp
	if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(CXX) -c -o $@ $(CXXFLAGS) $^	
	
%.o : %.C
	if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(AS) -c -o $@ $(ASFLAGS) $^	

%.hex : %.elf
	$(OBJCOPY) $^ -O ihex $@
	
%.dat : %.hex
	perl $(ROOTDIR)/common/scripts/objcopy_ihex2quartus_filter.pl \
		$^ $@

%.mem : %.elf
	$(OBJCOPY) $^ -O verilog $(@)
	perl $(COMMON_DIR)/scripts/objcopy_verilog_filter.pl $(@)

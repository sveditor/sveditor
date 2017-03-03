
all :
	@echo "SVEditor Build"
	@echo "  - build - build plug-ins"
	@echo "  - release - build plug-ins and push to repositories"

SCRIPTS_DIR := $(shell pwd)
SVEDITOR_DIR := $(shell cd $(SCRIPTS_DIR)/.. ; pwd)
ETC_DIR := $(shell cd $(SCRIPTS_DIR)/../etc ; pwd)

BUILD_DIR ?= $(SVEDITOR_DIR)/build
BUILD_RESULT_DIR ?= $(BUILD_DIR)/result

JAVA ?= $(shell which java)

uname_o:=$(shell uname -o)
uname_m:=$(shell uname -m)
MK_INCLUDES += ./packages.mk
MK_INCLUDES += $(ETC_DIR)/sveditor.info
WGET=wget

ECLIPSE_HOME=$(BUILD_DIR)/eclipse
export ECLIPSE_HOME
ECLIPSE=/bin/sh $(SCRIPTS_DIR)/eclipse.sh -data $(BUILD_DIRECTORY)/ws 
ANT=$(ECLIPSE) -application org.eclipse.ant.core.antRunner
INSTALL_IU=$(ECLIPSE) -application org.eclipse.equinox.p2.director

ifeq (Cygwin,$(uname_o))
  LAUNCHER_JAR=$(shell cygpath -w `ls $(BUILD_DIR)/eclipse/plugins/org.eclipse.equinox.launcher_*.jar` | sed -e 's%\\%/%g')
  BUILD_DIR_A=$(shell cygpath -w $(BUILD_DIR) | sed -e 's%\\%/%g')
  SCRIPTS_DIR_A=$(shell cygpath -w $(SCRIPTS_DIR) | sed -e 's%\\%/%g')
  os:=windows
  swt_os=win32
  swt_ws=win32
  ifeq (x86_64,$(uname_m))
    platform:=win64
    swt_arch=x86_64
  else
    platform:=win32
    swt_arch=i386
  endif
else
  LAUNCHER_JAR=$(wildcard $(BUILD_DIR)/eclipse/plugins/org.eclipse.equinox.launcher_*.jar)
  BUILD_DIR_A=$(BUILD_DIR)
  SCRIPTS_DIR_A=$(SCRIPTS_DIR)
endif


include $(MK_INCLUDES)

.PHONY: build release 

$(BUILD_DIR)/fetch-packages : $(PACKAGES)
	if test ! -d $(BUILD_DIR); then mkdir -p $(BUILD_DIR); fi
	touch $@

build : $(BUILD_DIR)/build_$(version)

ifeq ($(os),windows)
$(BUILD_DIR)/eclipse.init : $(BUILD_DIR)/fetch-packages
	if test ! -d $(BUILD_DIR); then mkdir -p $(BUILD_DIR); fi
	rm -rf $(BUILD_DIR)/eclipse 
	cd $(BUILD_DIR) ; unzip $(eclipse_build_pkg) 
	rm -rf $(BUILD_DIR)/gef 
	mkdir -p $(BUILD_DIR)/gef
	cd $(BUILD_DIR)/gef ; unzip $(PACKAGES_DIR)/$(zest_zip)
	$(INSTALL_IU) -repository file:/$(BUILD_DIR_A)/gef -tag AddZEST \
		-destination $(BUILD_DIR_A)/eclipse \
		-installIU org.eclipse.gef.feature.group \
		-installIU org.eclipse.draw2d.feature.group \
		-installIU org.eclipse.zest.feature.group
	touch $@
endif


$(BUILD_DIR)/build_$(version) : $(BUILD_DIR)/eclipse.init
	if test ! -d $(BUILD_DIR); then mkdir -p $(BUILD_DIR); fi
	rm -rf $(BUILD_DIR)/plugin_build
	mkdir -p $(BUILD_DIR)/plugin_build
	$(ANT) -buildfile $(SCRIPTS_DIR_A)/build.xml  \
		-DbuildDirectory=$(BUILD_DIR_A)/plugin_build \
		-DbuildResult=$(BUILD_DIR_A)/result \
		-Dos=$(swt_os) -Dws=$(swt_ws) -Darch=$(swt_arch) \
	build_core
	touch $@

release : $(BUILD_DIR)/build_$(version)
	$(ANT) -buildfile $(SCRIPTS_DIR_A)/release.xml  \
		-DbuildDirectory=$(BUILD_DIR_A)/plugin_build \
		-DbuildResult=$(BUILD_DIR_A)/result \
		-Drlsdir=$(BUILD_DIR_A)/rlsdir -verbose \
		-Dos=$(swt_os) -Dws=$(swt_ws) -Darch=$(swt_arch) release_core

RULES := 1

include $(MK_INCLUDES)



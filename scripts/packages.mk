
SCRIPTS_DIR := $(shell cd $(dir $(lastword $(MAKEFILE_LIST))); pwd)
PACKAGES_DIR := $(SCRIPTS_DIR)/../packages

ifneq (1,$(RULES))
mirror_ftp?=ftp://ftp.osuosl.org/pub/eclipse

#eclipse_build_version=4.7.3a
eclipse_build_version=4.12
eclipse_build_repo=http://download.eclipse.org/releases/neon
#eclipse_build_drop=R-$(eclipse_build_version)-201803300640
eclipse_build_drop=R-$(eclipse_build_version)-201906051800
eclipse_build_release=$(mirror_ftp)/eclipse/downloads/drops4/$(eclipse_build_drop)
eclipse_build_linux_tgz=eclipse-SDK-$(eclipse_build_version)-linux-gtk.tar.gz
eclipse_build_linux_x86_64_tgz=eclipse-SDK-$(eclipse_build_version)-linux-gtk-x86_64.tar.gz
eclipse_build_win32_zip=eclipse-SDK-$(eclipse_build_version)-win32.zip
eclipse_build_win32_x86_64_zip=eclipse-SDK-$(eclipse_build_version)-win32-x86_64.zip

# TODO: condition on platform
ifeq ($(platform),linux_x86_64)
   eclipse_build_pkg := $(PACKAGES_DIR)/$(eclipse_build_linux_x86_64_tgz)
else # Not Windows
  ifeq ($(platform),win64)
    eclipse_build_pkg := $(PACKAGES_DIR)/$(eclipse_build_win32_x86_64_zip)
  else
    eclipse_build_pkg := $(PACKAGES_DIR)/$(eclipse_build_win32_zip)
  endif
endif

PACKAGES += $(eclipse_build_pkg)

eclipse_run_version=4.6.1
eclipse_run_repo=http://download.eclipse.org/releases/neon
eclipse_run_drop=R-$(eclipse_run_version)-201609071200
eclipse_run_release=$(mirror_ftp)/eclipse/downloads/drops4/$(eclipse_run_drop)
eclipse_run_linux_tgz=eclipse-SDK-$(eclipse_run_version)-linux-gtk.tar.gz
eclipse_run_linux_x86_64_tgz=eclipse-SDK-$(eclipse_run_version)-linux-gtk-x86_64.tar.gz
eclipse_run_win32_zip=eclipse-SDK-$(eclipse_run_version)-win32.zip
eclipse_run_win32_x86_64_zip=eclipse-SDK-$(eclipse_run_version)-win32-x86_64.zip

eclipse_orbit_version=R20160520211859
eclipse_orbit_release=$(mirror_ftp)/tools/orbit/downloads/drops/$(eclipse_orbit_version)
eclipse_orbit_zip=orbit-buildrepo-$(eclipse_orbit_version).zip


emf_version=2.12.0
emf_release=modeling/emf/emf/downloads/drops/$(emf_version)/R201605260356
emf_zip=emf-xsd-Update-$(emf_version).zip

emf_transaction_version=1.10.0
emf_transaction_release=$(mirror_ftp)/modeling/emf/transaction/downloads/drops/$(emf_transaction_version)/R201606071900
emf_transaction_zip=emf-transaction-runtime-$(emf_transaction_version).zip

emf_validation_version=1.10.0
emf_validation_release=$(mirror_ftp)/modeling/emf/validation/downloads/drops/$(emf_validation_version)/R201606071713
emf_validation_zip=emf-validation-runtime-$(emf_validation_version).zip

zest_release=$(mirror_ftp)/tools/gef/downloads/drops/legacy/4.0.0/R201606061308
zest_zip=GEF3-Update-4.0.0.zip

# TODO: condition on platform
PACKAGES += $(PACKAGES_DIR)/$(zest_zip)

rcptt_version=2.1.0
rcptt_release=$(mirror_ftp)/rcptt/release/$(rcptt_version)
rcptt_zip=repository-$(rcptt_version).zip

rcptt_runner_release=$(mirror_ftp)/rcptt/release/$(rcptt_version)/runner
rcptt_runner_zip=rcptt.runner-2.1.0.zip


else

$(PACKAGES_DIR)/$(eclipse_build_win32_x86_64_zip) :
	$(Q)if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(WGET) -O $@ $(eclipse_build_release)/$(eclipse_build_win32_x86_64_zip)

$(PACKAGES_DIR)/$(eclipse_build_linux_x86_64_tgz) :
	$(Q)if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(WGET) -O $@ $(eclipse_build_release)/$(eclipse_build_linux_x86_64_tgz)

$(PACKAGES_DIR)/$(zest_zip) :
	$(Q)if test ! -d `dirname $@`; then mkdir -p `dirname $@`; fi
	$(WGET) -O $@ $(zest_release)/$(zest_zip)

endif


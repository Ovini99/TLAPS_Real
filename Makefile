# Copyright (C) 2008  INRIA and Microsoft Corporation

INSTALL = /usr/bin/install -c

prefix = /home/ovini/NFMDemo
exec_prefix = ${prefix}

srcdir          = .


bindir          = ${exec_prefix}/bin
LIBPATH		= ${exec_prefix}/lib/tlaps

all: check-configure tlapm

.PHONY:check-configure
check-configure: configure
	@if test "${srcdir}/configure" -nt "${srcdir}/Makefile" ; then \
	  echo "WARNING! ${srcdir}/configure is more recent than ${srcdir}/Makefile" ; \
	  echo "Running ${srcdir}/configure again..." ; \
	  ${MAKE} same-justconf CONFIGARGS="--silent" ; \
	  echo "Finished ${srcdir}/configure; 'make' will now exit." ; \
	  echo "Please run 'make' again to continue." ; \
	  exit 1 ; \
	fi

.PHONY: tlapm
tlapm:
	rm -f tlapm
	${MAKE} -C src tlapm.native
	cp src/tlapm.native tlapm

.PHONY: utest
utest:
	: ----------------------- unit tests ----------------------
	${MAKE} -C src utest
	RESOURCE_FOLDER=test/resources/ src/tlapm.byte --version

.PHONY: test
test:
	: ----------------------- unit tests ----------------------
	${MAKE} -C src clean >/dev/null 2>&1
	${MAKE} -C src utest
	RESOURCE_FOLDER=test/resources/ src/tlapm.byte --version
	${MAKE} -C src clean >/dev/null 2>&1
	: --------------------fast regression tests -------------------
	${MAKE} tlapm >/dev/null 2>&1
	cd test && ${MAKE}
	${MAKE} clean >/dev/null 2>&1

.PHONY: jtest
jtest:
	: ----------------------- unit tests ----------------------
	${MAKE} -C src clean >/dev/null 2>&1
	${MAKE} -C src utest
	Jenkins=1 RESOURCE_FOLDER=test/resources/ src/tlapm.byte --version
	${MAKE} -C src clean >/dev/null 2>&1
	: -------------------- soundness tests -------------------
	${MAKE} tlapm >/dev/null 2>&1
	cd test && ${MAKE} stest
	: -------------------- regression tests -------------------
	cd test && ${MAKE} junit
	${MAKE} clean >/dev/null 2>&1

.PHONY: testall
testall:
	cd test && ${MAKE} all

.PHONY: clean
clean:
	${MAKE} -C src clean
	rm -f tlapm

.PHONY: distclean
distclean: clean
	rm -f config.*
	rm -rf autom4te.*
	rm -f Makefile myocamlbuild.ml src/config.ml src/load.ml
	rm -f tools/installer/tlaps-release.sh
	rm -f tools/installer/tlaps-source-release.sh


FORMATTING_FILE_TYPES = \
  -e thy \
  -e ml -e mli -e mll -e mlt \
  -e pxd -e pxi -e py -e pyx \
  -e sh \
  -e tla
FORMATTING_FILE_REGEX = \
  '\.(ml|mli|mll|mlt|pxd|pxi|pyx|sh|thy|tla)$$'


# Formatting rules below require the packages:
# - `coreutils` (contains `gexpand`, `gtr`)
# - `moreutils` (contains `sponge`)
# - `ag`
# - `as-tree`
# - `fd`


.PHONY: format_tab_space_dryrun
# detect and print Isabelle, OCaml, Python, Shell, TLA+ files with:
# - trailing blanks (\t and \s)
# - leading tabs (\t)
# - tabs (\t)
# - CR characters
format_tab_space_dryrun:
	@echo $$'\nsearching for files with extensions:\n'
	@echo ${FORMATTING_FILE_REGEX}
	@echo $$'\nfiles that contain tabs within leading blanks:\n'
	ag --file-search-regex ${FORMATTING_FILE_REGEX} \
	    --files-with-matches \
	    '^\s*\t' . \
	    | as-tree
	@echo $$'\nfiles that contain tabs anywhere:\n'
	ag --file-search-regex ${FORMATTING_FILE_REGEX} \
	    --files-with-matches '\t' . \
	    | as-tree
	@echo $$'\nfiles that contain trailing blank space:\n'
	ag --file-search-regex ${FORMATTING_FILE_REGEX} \
	    --files-with-matches '( |\t)$$' . \
	    | as-tree
	@echo $$'\nany files that contain CR:\n'
	ag --files-with-matches $$'\r' . | as-tree


.PHONY: expand_tabs
expand_tabs:
	@echo $$'\nreplace each tab by 4 spaces\n'
	time fd -t f ${FORMATTING_FILE_TYPES} \
	    --exec bash -c \
	        "gexpand -i -t 4 {} \
	            | sponge {}" ';'


.PHONY: rm_cr
# `sponge` is not used in this case,
# because in case the Python script
# finds any `\r` outside of `\r\n`,
# it raises an exception, and then
# the file should remain unchanged.
rm_cr:
	@echo $$'\nremove CR characters'
	time fd -t f ${FORMATTING_FILE_TYPES} \
	    --exec bash -c \
	        "python tools/change_blank_space.py \
	            --rm-cr {}" ';'


.PHONY: rm_trailing
rm_trailing:
	@echo $$'\nremove trailing blank space'
	time fd -t f ${FORMATTING_FILE_TYPES} \
	    --exec bash -c \
	        "python tools/change_blank_space.py \
	            --rm-trailing-blank {}" ';'


.PHONY: allinstall
allinstall: all
	${MAKE} install

.PHONY: install
install:
	mkdir -p -m 0755 ${bindir}
	${INSTALL} -s -m 0755 tlapm ${bindir}
	@if test "x${SILENT}" != xyes ; then \
	  echo '' ; \
	  echo 'The TLA+ Proof Manager (tlapm) has been installed to' ; \
	  echo '' ; \
	  echo '        ' ${bindir} ; \
	  echo '' ; \
	  if test "no`which tlapm`" = "no" ; then \
	    echo '' ; \
	    echo "WARNING: ${bindir} is not in your PATH" ; \
	  fi ; \
	fi
	mkdir -p -m 0755 ${LIBPATH}
	${INSTALL} -m 0644 library/*.tla ${LIBPATH}
	/usr/bin/tar -cf - examples | ( cd ${LIBPATH} && /usr/bin/tar -xf - )

.PHONY: uninstall
uninstall:
	rm -f ${bindir}/tlapm
	if test -n "`ls -A ${LIBPATH}`"; \
	  then rm -rf ${LIBPATH} ; \
	fi

.PHONY: newversion
newversion:
	ocaml str.cma unix.cma tools/newversion.ml ${NEWVERARGS}

.PHONY: release
release:
	ocaml str.cma unix.cma tools/newversion.ml -release ${NEWVERARGS}

.PHONY: sameversion
sameversion:
	${MAKE} newversion NEWVERARGS="-same"

.PHONY: same
same:
	@  ${MAKE} same-justconf CONFIGARGS="--silent" \
	&& ${MAKE} SILENT=yes all

.PHONY: same-justconf
same-justconf:
	./configure ${CONFIGARGS} \
	  --prefix /home/ovini/NFMDemo \
	  --enable-debugging=no \
	  --enable-profiling=no

.PHONY: same-full
same-full:
	@  ${MAKE} newversion NEWVERARGS="-quiet -same" \
	&& ${MAKE} same-justconf CONFIGARGS="--silent" \
	&& ${MAKE} SILENT=yes all

.PHONY: emacs
emacs:
	svn --force export svn+ssh://${MSR_SVN_USER}@svn.msr-inria.inria.fr/var/lib/svn/repository/tla/trunk/misc/tla_mode doc/web/tla_mode

.PHONY: web
web: same-justconf emacs

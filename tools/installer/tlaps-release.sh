#!/bin/bash

set -e

error() {
    printf "%s\n" >&2
    exit 3
}

OLDPWD="`pwd`"

TLAPSVER="$(echo "tlaps-1.5.0" | sed -e 's/ /_/g')-x86_64-linux-gnu"

case "" in
  "") TARGET_FILE="$TLAPSVER-inst.bin";;
  *) TARGET_FILE="$TLAPSVER-inst";;
esac
TARGET="$OLDPWD/$TARGET_FILE"
GIT_BRANCH="`git rev-parse --abbrev-ref HEAD`"
PS_DIR="$(pwd)/../.."
PM_DIR="$(pwd)/../.."

cat <<EOF

This script builds a binary distribution of the TLA+ Proof System
version 1.5.0, compiled with OCaml version 4.13.1.

Target: ${TARGET}
Git branch: ${GIT_BRANCH}

EOF

case $OLDPWD in
    */installer) ;;
    *) error 'This script must be launched in the "installer" directory';;
esac

git_export() {
    (cd "$1" && git archive --format=tar HEAD "$2") | tar xf -
}

STEPNO=0
banner() {
    case $STEPNO in
    0) ;;
    *) cat <<-EOF

	   *** SUCCESS ***

	EOF
    ;;
    esac
    STEPNO=$((STEPNO + 1))
    cat <<-EOF
	${STEPNO}. $1

	EOF
}

download () {
    # usage: download <name> <dir> <file>
    # checks for already-downloaded file, downloads if needed,
    # and prints corresponding message.
    # Note: changes the current directory to $DOWNDIR
    cd "$DOWNDIR"
    if test -f "$3" ; then
        echo "   [x] $1 ALREADY downloaded"
    else
        /usr/bin/wget -q "$2/$3"
        echo "   [x] $1 distribution downloaded"
    fi
}

################################################################################

TLAPSDIR="$PS_DIR/$TLAPSVER"
DOWNDIR="$TLAPSDIR/download"
BUILDDIR="$TLAPSDIR/build"
INSTDIR="$TLAPSDIR/install"

banner "Setting up directories"
rm -rf "$BUILDDIR" "$INSTDIR"
mkdir -p "$DOWNDIR"
echo "   [x] Created $DOWNDIR"
mkdir -p "$BUILDDIR"
echo "   [x] Created $BUILDDIR"
mkdir -p "$INSTDIR"
echo "   [x] Created $INSTDIR"

################################################################################

ISABELLE=Isabelle2011-1
banner "Downloading and packaging $ISABELLE"

case "linux-gnu" in
  *linux*)  ISA_ARCHIVE="${ISABELLE}_bundle_x86-linux.tar.gz"
            ISA_ARCHIVE_TYPE=tgz
            ADD_GMP_DLL=false
            ;;
  *cygwin*) ISA_ARCHIVE="${ISABELLE}_bundle_x86-cygwin.tar.gz"
            ISA_ARCHIVE_TYPE=tgz
            ADD_GMP_DLL=true
            ;;
  *darwin*) ISA_ARCHIVE="${ISABELLE}.dmg"
            ISA_ARCHIVE_TYPE=dmg
            ADD_GMP_DLL=false
            ;;
  *) echo "unknown architecture: linux-gnu" >&2; exit 3;;
esac

mkdir -p "$INSTDIR/lib/tlaps"

download "$ISABELLE" "http://isabelle.in.tum.de/website-$ISABELLE/dist" \
         "$ISA_ARCHIVE"

case "$ISA_ARCHIVE_TYPE" in
  tgz) tar -C "$INSTDIR/lib/tlaps" -xzf "$ISA_ARCHIVE";;
  dmg) hdiutil attach "$ISA_ARCHIVE" -quiet -readonly -nobrowse \
               -mountpoint "$DOWNDIR/dmg"
       cp -a "$DOWNDIR/dmg/$ISABELLE.app/Contents/Resources/$ISABELLE" \
          "$INSTDIR/lib/tlaps/"
       hdiutil detach "$DOWNDIR/dmg" -quiet
       ;;
  *) echo "unknown archive type: $ISA_ARCHIVE_TYPE" >&2; exit 3;;
esac
if $ADD_GMP_DLL; then
    (
        cd $INSTDIR/lib/tlaps/$ISABELLE/contrib/polyml-5.4.0/x86-cygwin
        git_export "$PS_DIR/misc" cyggmp-3.dll
    )
fi
echo "   [x] $ISABELLE extracted"

cd "$INSTDIR/lib/tlaps"
ISABELLE_DELETEDS=$(echo $ISABELLE/contrib/ProofGeneral* $ISABELLE/doc $ISABELLE/heaps/*/HOL $ISABELLE/lib/{classes,fonts,logo})
rm -rf $ISABELLE_DELETEDS
echo $ISABELLE_DELETEDS | xargs -n 1 echo '   [x] Trimmed'
cat >"$ISABELLE/README.TLAPS" <<EOF
The following files and directories have been deleted from
the default $ISABELLE distribution:

$(echo ${ISABELLE_DELETEDS} | xargs -n 1 echo ' *')

  -- TLAPS Maintainers <tlaps-devel@list.gforge.inria.fr>
     $(date +%Y/%m/%d)
EOF

ln -s -f "$ISABELLE" Isabelle

mkdir -p bin
cd bin
ln -s -f "../$ISABELLE/bin/isabelle"
ln -s -f "../$ISABELLE/bin/isabelle-process"

################################################################################

banner "Exporting Isabelle/TLA+"

mkdir -p "$INSTDIR/lib/tlaps"
cd "$INSTDIR/lib/tlaps"

mkdir isabelle-tmp && (
    cd isabelle-tmp &&
    git_export "$PS_DIR" isabelle && mv isabelle ../TLA+
) && rmdir isabelle-tmp
echo "   [x] Exported"

################################################################################

banner "Exporting and building Zenon"

cd "$BUILDDIR"

git_export "$PS_DIR" zenon
echo "   [x] Exported"

( set -x
  cd zenon
  ./configure -coqc : -bindir "$INSTDIR/lib/tlaps/bin" \
              -libdir "$INSTDIR/lib/tlaps"
  make
  make install
) > zenon-build.log 2>&1
echo "   [x] Built"

################################################################################

# CVC4_VERS=1.5
# CVC4=CVC4-$CVC4_VERS
# banner "Downloading and packaging $CVC4"

# case "linux-gnu" in
#   *linux*)  CVC_DIR=https://tla.msr-inria.inria.fr/tlaps/dist/cvc4
#             CVC_FILE=cvc4-1.5-x86_64-linux-opt
#             ;;
#   *cygwin*) CVC_DIR=https://tla.msr-inria.inria.fr/tlaps/dist/cvc4
#             CVC_FILE=cvc4-1.5-win32-opt.exe
#             ;;
#   *darwin*) CVC_DIR=https://tla.msr-inria.inria.fr/tlaps/dist/cvc4
#             CVC_FILE=cvc4-1.5-x86_64-macos-10.12-opt
#             ;;
#   *) echo "unknown architecture: linux-gnu" >&2; exit 3;;
# esac

# mkdir -p "$INSTDIR/lib/tlaps/bin"

# cd "$DOWNDIR"
# if test -f "$CVC_FILE" ; then
#     echo "   [x] $CVC4 ALREADY downloaded"
# else
#     /usr/bin/wget -q "$CVC_DIR/$CVC_FILE"
#     echo "   [x] $CVC4 distribution downloaded"
# fi

# chmod +x "$CVC_FILE"
# cp "$CVC_FILE" "$INSTDIR/lib/tlaps/bin/cvc4"

# echo "   [x] $CVC4 extracted"

################################################################################

Z3_VERS=4.8.9
Z3=Z3-$Z3_VERS
banner "Downloading and packaging $Z3"

Z3_DIR=https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERS}
case "linux-gnu" in
  *linux*)  Z3_FILE=z3-${Z3_VERS}-x64-ubuntu-16.04
            ;;
  *cygwin*) Z3_FILE=z3-${Z3_VERS}-x86-win
            ;;
  *darwin*) Z3_FILE=z3-${Z3_VERS}-x64-osx-10.14.6
            ;;
  *) echo "unknown architecture: linux-gnu" >&2; exit 3;;
esac

mkdir -p "$INSTDIR/lib/tlaps/bin"

download "$Z3" "$Z3_DIR" "$Z3_FILE".zip

unzip -q -o "$Z3_FILE".zip
cp "$Z3_FILE"/bin/z3 "$INSTDIR"/lib/tlaps/bin/
chmod a+x "$INSTDIR"/lib/tlaps/bin/z3

echo "   [x] $Z3 extracted"

################################################################################

LS4_VERS=1.0
LS4="LS4-$LS4_VERS"
LS4_FILE="v$LS4_VERS.zip"
banner "Downloading and building $LS4"

download "$LS4" "https://github.com/quickbeam123/ls4/archive" "$LS4_FILE"

cd "$BUILDDIR"

unzip -q -d ls4 "$DOWNDIR/$LS4_FILE"

( set -x
  patch -p0 <<EOF
--- ls4.orig/ls4-1.0/core/SolverTypes.h	2017-06-27 16:23:41.000000000 +0200
+++ ls4/ls4-1.0/core/SolverTypes.h	2017-06-27 16:23:52.000000000 +0200
@@ -47,7 +47,7 @@
     int     x;
     
     // Use this as a constructor:
-    friend Lit mkLit(Var var, bool sign = false);
+    friend Lit mkLit(Var var, bool sign);
 
     bool operator == (Lit p) const { return x == p.x; }
     bool operator != (Lit p) const { return x != p.x; }
@@ -55,7 +55,7 @@
 };
 
 
-inline  Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }
+inline  Lit  mkLit     (Var var, bool sign = false) { Lit p; p.x = var + var + (int)sign; return p; }
 inline  Lit  operator ~(Lit p)              { Lit q; q.x = p.x ^ 1; return q; }
 inline  Lit  operator ^(Lit p, bool b)      { Lit q; q.x = p.x ^ (unsigned int)b; return q; }
 inline  bool sign      (Lit p)              { return p.x & 1; }
EOF
  cd ls4/ls4-*/core
  cc -c aiger.c
  make
  mkdir -p "$INSTDIR/lib/tlaps/bin"
  cp ls4 "$INSTDIR/lib/tlaps/bin/"
) > ls4-build.log 2>&1
echo "   [x] Built"

################################################################################

banner "Exporting and building the 'translate' utility"

cd "$BUILDDIR"

git_export "$PS_DIR" translate
echo "   [x] Exported"

( set -x
  cd translate
  ./buildb.sh
  mkdir -p "$INSTDIR/lib/tlaps/bin"
  cp translate.bin "$INSTDIR/lib/tlaps/bin/translate"
  cp translate.bin "$INSTDIR/lib/tlaps/bin/ptl_to_trp"
) > translate-build.log 2>&1
echo "   [x] Built"

################################################################################

banner "Exporting and building the TLA+ Proof Manager (tlapm)"

cd "$BUILDDIR"

(mkdir tlapm && cd tlapm && git_export "$PM_DIR" .)
echo "   [x] Exported"

( set -x
  cd tlapm
  ./configure --prefix "$INSTDIR"
  make all install
) > tlapm-build.log 2>&1
echo "   [x] Built"

################################################################################

banner "Exporting tla-mode"

cd "$INSTDIR"

mkdir -p lib/tlaps/emacs
(cd lib/tlaps/emacs && git_export "$PS_DIR/misc" tla_mode)
echo "   [x] Exported"

################################################################################

banner "Creating the uninstaller"

UNINST_FILE=un-inst
UNINSTALLER="$INSTDIR/lib/tlaps/$UNINST_FILE"

UNINSTALLER_SOURCE="$BUILDDIR/uninstall.ml"
cat > "$UNINSTALLER_SOURCE" <<EOF
let flush_all () =
  flush stdout ;
  flush stderr

open Unix
open Printf

let verbose_unlink path =
  printf "UNLINK %s\n" path ;
  unlink path ;
  flush_all ()

let verbose_rmdir path =
  printf "RMDIR %s\n" path ;
  rmdir path ;
  flush_all ()

let output_dir =
  let d = Sys.executable_name in (* dest/lib/tlaps/$UNINST_FILE *)
  let d = Filename.dirname d in  (* dest/lib/tlaps *)
  let d = Filename.dirname d in  (* dest/lib *)
  let d = Filename.dirname d in  (* dest *)
  d

let path ents = match ents with
  | [] -> "/"
  | head :: rest ->
     List.fold_left Filename.concat head rest

let fatal_error fmt =
  output_string Stdlib.stderr "FATAL ERROR: " ;
  kfprintf
    (fun _ ->
       output_string Stdlib.stderr "\\n\\n    *** ABORT ***.\\n" ;
       flush Stdlib.stderr ;
       Stdlib.exit 2)
    Stdlib.stderr fmt

let rm_ifempty path = try begin
  let d = opendir path in
  let rec spin k =
    try ignore (readdir d) ; spin (k + 1) with End_of_file -> k in
  if spin 0 = 2 then verbose_rmdir path
end with _ -> ()

let rm_f path =
  try verbose_unlink path with _ -> ()

let rec rm_rf dir = try begin
  let d = opendir dir in
  let rec spin () =
    try begin
      match readdir d with
        | "." | ".." -> spin ()
        | ent ->
            let ent = Filename.concat dir ent in
            let st = lstat ent in
            begin match st.st_kind with
              | S_DIR -> rm_rf ent
              | _ -> rm_f ent
            end ;
            spin ()
    end with
      | End_of_file -> closedir d
  in
  spin () ;
  verbose_rmdir dir
end with _ -> ()

let () =
  printf "Uninstalling the TLA+ Proof System\\n" ;
  printf "version 1.5.0 from:\\n" ;
  printf "    %s\\n" output_dir ;
  flush_all () ;
  rm_f (path [ output_dir ; "bin" ; "tlapm" ]) ;
  rm_ifempty (path [ output_dir ; "bin" ]) ;
  rm_rf (path [ output_dir ; "lib" ; "tlaps" ]) ;
  rm_ifempty (path [ output_dir ; "lib" ; "tlaps" ]) ;
  rm_ifempty (path [ output_dir ; "lib" ]) ;
  rm_ifempty (path [ output_dir ]) ;
  printf "Done.\\n" ;
  flush_all ()

EOF

ocamlopt -o "$UNINSTALLER" unix.cmxa "$UNINSTALLER_SOURCE"

################################################################################

banner "Creating $TLAPSVER.tar.gz"

cd "$INSTDIR"
rm -f "../$TLAPSVER.tar.gz"

tar --create --gzip --file="../$TLAPSVER.tar.gz" *

################################################################################

banner "Assembling $TARGET"

cd "$TLAPSDIR"

TAR_SIZE=$(wc -c < "$TLAPSVER.tar.gz")
if test $? -ne 0 ; then
    cat <<EOF
   *** Could not compute the size of ${TLAPSVER}.tar.gz ***

Aborted.
EOF
    exit 2
fi

SOURCE="$BUILDDIR/tlaps_release.ml"

rm -f "$TARGET" "$SOURCE"

cat > "$SOURCE" <<EOF
(* This file is automatically generated -- do not edit! *)

let flush_all () =
  flush stdout ;
  flush stderr

let buf_len = 8192

let input_all ic =
  let rec loop acc total buf ofs =
    let n = input ic buf ofs (buf_len - ofs) in
    if n = 0 then
      let res = Bytes.create total in
      let pos = total - ofs in
      let _ = Bytes.blit buf 0 res pos ofs in
      let coll pos buf =
        let new_pos = pos - buf_len in
        Bytes.blit buf 0 res new_pos buf_len;
        new_pos in
      let _ = List.fold_left coll pos acc in
      res
    else
      let new_ofs = ofs + n in
      let new_total = total + n in
      if new_ofs = buf_len then
        loop (buf :: acc) new_total (Bytes.create buf_len) 0
      else loop acc new_total buf new_ofs in
  loop [] 0 (Bytes.create buf_len) 0

let input_file ?(bin=false) fname =
  let ch = (if bin then open_in_bin else open_in) fname in
  let str = input_all ch in
  close_in ch;
  str

open Unix
open Str
open Printf

let output_dir = ref "/usr/local"

let fatal_error fmt =
  output_string Pervasives.stderr "FATAL ERROR: " ;
  kfprintf
    (fun _ ->
       output_string Pervasives.stderr "\\n\\n    *** ABORT ***.\\n" ;
       flush Pervasives.stderr ;
       Pervasives.exit 2)
    Pervasives.stderr fmt

let () =
  Arg.parse [ "-d", Arg.Set_string output_dir, "Set the install directory" ]
    (fun arg -> fatal_error "Bad arguments %S" arg)
    "$TARGET_FILE [-d DIR]"

let () =
  if Filename.is_relative !output_dir then
    output_dir := Filename.concat (getcwd ()) !output_dir

let fails fn =
  try (fn () ; false)
  with ex ->
    Printf.eprintf "\nEXCEPTION: %s\n%!" (Printexc.to_string ex) ;
    true

let path ents = match ents with
  | [] -> "/"
  | head :: rest ->
     List.fold_left Filename.concat head rest

let maybe_unlink fn =
  if Sys.file_exists fn then unlink fn else ()

let () =
  printf "Installing the TLA+ Proof System\\n\\n" ;
  printf "    Version: 1.5.0\\n" ;
  printf "Destination: %s\\n\\n" !output_dir ;
  flush_all () ;
  let old_uninst = path [ !output_dir ; "lib" ; "tlaps" ; "$UNINST_FILE" ] in
  if Sys.file_exists old_uninst then begin
    printf "\\nThere appears to be an installation of TLAPS already in %s.\\n"
           !output_dir ;
    printf "Running its uninstaller...\\n" ;
    flush_all () ;
    let unret = Sys.command old_uninst in
    if unret <> 0 then
      eprintf "Error in running the old uninstaller! Continuing anyway...\\n" ;
    flush_all () ;
  end ;
  if Sys.command ("mkdir -p " ^ !output_dir) <> 0 then
    fatal_error "Cannot create %s." !output_dir ;
  let ost = lstat !output_dir in
  if ost.st_kind != S_DIR then
    fatal_error "%s already exists but is not a directory." !output_dir ;
  if fails begin fun () ->
    let p = path [ !output_dir ; ".test" ] in
    let f = open_out p in
    close_out f ; maybe_unlink p
  end then
    fatal_error "Cannot write to %s." !output_dir ;
  printf "Extracting ... " ;
  flush_all () ;
  let tar_cmd =
    Printf.sprintf "tail -c ${TAR_SIZE} \\"%s\\" | tar -xzp -C %s -f -"
      Sys.executable_name !output_dir in
  if Sys.command tar_cmd <> 0 then
    fatal_error "Could not extract into %s." !output_dir ;
  printf "done.\\n" ;
  printf "Compiling Isabelle theories.\\n" ;
  flush_all () ;
  let isabelle_settings_file =
    path [ !output_dir ; "lib" ; "tlaps" ; "Isabelle" ; "etc" ; "settings" ] in
  let isabelle_settings = input_file ~bin:true isabelle_settings_file in
  let isabelle_settings_modified =
    replace_first
      (regexp "^ISABELLE_HOME_USER=.*\$")
      ("ISABELLE_HOME_USER=" ^ path [ !output_dir ; "lib" ; "tlaps" ])
      (Bytes.to_string isabelle_settings) in
  if (Bytes.to_string isabelle_settings) = isabelle_settings_modified then
    fatal_error "Could not modify %s." isabelle_settings_file ;
  let isabelle_settings_modified2 =
    replace_first
      (regexp "^ML_PLATFORM=\"\\\\\$ISABELLE_PLATFORM\"\$")
      "ML_PLATFORM=\"\${ISABELLE_PLATFORM64:-\$ISABELLE_PLATFORM}\""
      isabelle_settings_modified in
  if isabelle_settings_modified = isabelle_settings_modified2 then
    fatal_error "Could not modify %s." isabelle_settings_file ;
  if fails begin fun () ->
    let f = open_out_bin isabelle_settings_file in
    output_string f isabelle_settings_modified2 ;
    close_out f
  end then
    fatal_error "Could not overwrite %s." isabelle_settings_file ;
  let pure_cmd = Printf.sprintf
    "cd %s && ../../bin/isabelle make"
    (path [ !output_dir ; "lib" ; "tlaps" ; "Isabelle" ; "src" ; "Pure" ]) in
  if Sys.command pure_cmd <> 0 then
    fatal_error "Could not compile Isabelle/Pure" ;
  let tla_plus_cmd = Printf.sprintf
    "cd %s && ../Isabelle/bin/isabelle usedir -b Pure TLA+"
    (path [ !output_dir ; "lib" ; "tlaps" ; "TLA+" ]) in
  if Sys.command tla_plus_cmd <> 0 then
    fatal_error "Could not compile Isabelle/TLA+" ;
  printf "Finished compiling Isabelle theories.\\n" ;
  printf "Performing a self-test ... " ;
  flush_all () ;
  if fails begin fun () ->
    let cmd = Printf.sprintf
      "cd %s/lib/tlaps; %s/bin/tlapm -C -I +examples/cantor Cantor1.tla > Cantor1.log 2>&1"
      !output_dir !output_dir in
    if Sys.command cmd <> 0 then
      failwith "self-test failed" ;
    maybe_unlink (path [!output_dir ; "lib/tlaps/Cantor1.log"]) ;
  end then
     fatal_error "Self-test unsuccessful!" ;
  printf "done.\\n" ;
  printf "\\nAll done.\\n\\n" ;
  flush_all () ;
  printf "REMEMBER to add %s to your \$PATH\\n"
    (path [ !output_dir ; "bin" ]) ;
  printf "You will also need to add\\n   %!";
  let p = path [ !output_dir ; "lib"; "tlaps" ] in
  begin match Sys.os_type with
  | "Cygwin" ->
     let cmd = sprintf "cygpath -d %s\\n" (Filename.quote p) in
     ignore (Sys.command cmd);
  | _ -> printf "%s\\n" p;
  end;
  printf "to the toolbox's library path \\
          (File->Preferences->TLA+ Preferences->Add Directory)\\n\\n";
  flush_all ()

EOF

ocamlopt -w -3 -o "$TARGET" unix.cmxa str.cmxa "$SOURCE"
strip "$TARGET" || exit 0
cat "$TLAPSVER.tar.gz" >> "$TARGET"
rm -f "$TLAPSVER.tar.gz"

################################################################################

cat <<EOF

   *** SUCCESS ***

All done.

The file ${TARGET} is now ready to distribute.

EOF

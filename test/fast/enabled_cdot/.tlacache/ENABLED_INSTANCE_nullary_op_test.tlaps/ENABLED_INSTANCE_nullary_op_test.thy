(* automatically generated -- do not edit manually *)
theory ENABLED_INSTANCE_nullary_op_test imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'1:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
shows "(\<exists>a_CONSTANTunde_rhash_0unde_a : (a_CONSTANTunde_rhash_0unde_a))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/ENABLED_INSTANCE_nullary_op_test.tlaps/tlapm_dad0e0.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/ENABLED_INSTANCE_nullary_op_test.tlaps/tlapm_dad0e0.znn.out
;; obligation #1
$goal (E. ((a_CONSTANTunde_rhash_0unde_a) a_CONSTANTunde_rhash_0unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(\\E a_CONSTANTunde_rhash_0unde_a:a_CONSTANTunde_rhash_0unde_a))" (is "~(\\E x : ?z_hd(x))")
 have z_He: "~?z_hd(TRUE)" (is "~?z_hf")
 by (rule zenon_notex_0 [of "?z_hd" "?z_hf", OF z_Ha])
 show FALSE
 by (rule zenon_nottrue [OF z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

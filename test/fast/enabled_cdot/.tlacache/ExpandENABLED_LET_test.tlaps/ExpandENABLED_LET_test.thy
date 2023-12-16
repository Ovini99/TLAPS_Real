(* automatically generated -- do not edit manually *)
theory ExpandENABLED_LET_test imports Constant Zenon begin
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
shows "(((a_VARIABLEunde_xunde_a) \<Rightarrow> (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((a_VARIABLEunde_xunde_a) & (a_CONSTANTunde_xhash_enabledhash_prime1unde_a)))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/ExpandENABLED_LET_test.tlaps/tlapm_15517b.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/ExpandENABLED_LET_test.tlaps/tlapm_15517b.znn.out
;; obligation #1
$goal (=> a_VARIABLEunde_xunde_a
(E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ a_VARIABLEunde_xunde_a
a_CONSTANTunde_xhash_enabledhash_prime1unde_a))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(a_VARIABLEunde_xunde_a=>(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(a_VARIABLEunde_xunde_a&a_CONSTANTunde_xhash_enabledhash_prime1unde_a))))" (is "~(_=>?z_hd)")
 have z_Hc: "a_VARIABLEunde_xunde_a"
 by (rule zenon_notimply_0 [OF z_Ha])
 have z_Hg: "(~?z_hd)" (is "~(\\E x : ?z_hh(x))")
 by (rule zenon_notimply_1 [OF z_Ha])
 have z_Hi: "~?z_hh(TRUE)" (is "~(_&?z_hj)")
 by (rule zenon_notex_0 [of "?z_hh" "?z_hj", OF z_Hg])
 show FALSE
 proof (rule zenon_notand [OF z_Hi])
  assume z_Hk:"(~a_VARIABLEunde_xunde_a)"
  show FALSE
  by (rule notE [OF z_Hk z_Hc])
 next
  assume z_Hl:"(~?z_hj)"
  show FALSE
  by (rule zenon_nottrue [OF z_Hl])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

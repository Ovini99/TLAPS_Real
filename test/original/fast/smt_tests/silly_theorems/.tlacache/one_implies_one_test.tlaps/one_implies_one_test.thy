(* automatically generated -- do not edit manually *)
theory one_implies_one_test imports Constant Zenon begin
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
shows "((((Succ[0])) \<Rightarrow> ((Succ[0]))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/one_implies_one_test.tlaps/tlapm_74b43c.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/one_implies_one_test.tlaps/tlapm_74b43c.znn.out
;; obligation #1
$goal (=> (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(1=>1))" (is "~(?z_hc=>_)")
 have z_Hc: "?z_hc"
 by (rule zenon_notimply_0 [OF z_Ha])
 have z_Hd: "(~?z_hc)"
 by (rule zenon_notimply_1 [OF z_Ha])
 show FALSE
 by (rule notE [OF z_Hd z_Hc])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

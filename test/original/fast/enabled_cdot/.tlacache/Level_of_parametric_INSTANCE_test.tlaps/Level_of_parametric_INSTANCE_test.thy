(* automatically generated -- do not edit manually *)
theory Level_of_parametric_INSTANCE_test imports Constant Zenon begin
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
(* usable definition CONSTANT_M!Foo_ suppressed *)
shows "((((a_CONSTANTunde_Mexcl_Foounde_a ((TRUE)))) \<Rightarrow> ((a_CONSTANTunde_Mexcl_Foounde_a ((TRUE))))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/Level_of_parametric_INSTANCE_test.tlaps/tlapm_5e7897.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Level_of_parametric_INSTANCE_test.tlaps/tlapm_5e7897.znn.out
;; obligation #1
$goal (=> (a_CONSTANTunde_Mexcl_Foounde_a T.)
(a_CONSTANTunde_Mexcl_Foounde_a T.))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(a_CONSTANTunde_Mexcl_Foounde_a(TRUE)=>a_CONSTANTunde_Mexcl_Foounde_a(TRUE)))" (is "~(?z_hc=>_)")
 have z_Hc: "?z_hc"
 by (rule zenon_notimply_0 [OF z_Ha])
 have z_He: "(~?z_hc)"
 by (rule zenon_notimply_1 [OF z_Ha])
 show FALSE
 by (rule notE [OF z_He z_Hc])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

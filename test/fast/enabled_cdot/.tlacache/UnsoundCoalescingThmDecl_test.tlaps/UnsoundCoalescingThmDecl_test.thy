(* automatically generated -- do not edit manually *)
theory UnsoundCoalescingThmDecl_test imports Constant Zenon begin
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
assumes v'8: "(((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((((~ ((~ (a_CONSTANTunde_xhash_enabledhash_prime1unde_a))))) \<and> ((~ (a_CONSTANTunde_xhash_enabledhash_prime1unde_a)))))) \<Leftrightarrow> ((((~ ((~ ((a_VARIABLEunde_xunde_hash_primea :: c)))))) \<and> (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((~ (a_CONSTANTunde_xhash_enabledhash_prime1unde_a))))))))"
assumes v'9: "((a_VARIABLEunde_xunde_hash_primea :: c))"
shows "(FALSE)"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/UnsoundCoalescingThmDecl_test.tlaps/tlapm_136189.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/UnsoundCoalescingThmDecl_test.tlaps/tlapm_136189.znn.out
;; obligation #1
$hyp "v'8" (<=> (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (-. (-. a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
(-. a_CONSTANTunde_xhash_enabledhash_prime1unde_a))))
(/\ (-. (-. a_VARIABLEunde_xunde_hash_primea))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (-. a_CONSTANTunde_xhash_enabledhash_prime1unde_a)))))
$hyp "v'9" a_VARIABLEunde_xunde_hash_primea
$goal F.
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((~(~a_CONSTANTunde_xhash_enabledhash_prime1unde_a))&(~a_CONSTANTunde_xhash_enabledhash_prime1unde_a)))<=>((~(~a_VARIABLEunde_xunde_hash_primea))&(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(~a_CONSTANTunde_xhash_enabledhash_prime1unde_a))))" (is "?z_hd<=>?z_hi")
 using v'8 by blast
 have z_Hb:"a_VARIABLEunde_xunde_hash_primea"
 using v'9 by blast
 assume z_Hc:"(~FALSE)" (is "~?z_hm")
 show FALSE
 proof (rule zenon_equiv [OF z_Ha])
  assume z_Hn:"(~?z_hd)" (is "~(\\E x : ?z_ho(x))")
  assume z_Hp:"(~?z_hi)" (is "~(?z_hj&?z_hl)")
  show FALSE
  proof (rule zenon_notand [OF z_Hp])
   assume z_Hq:"(~?z_hj)" (is "~~?z_hk")
   have z_Hk: "?z_hk"
   by (rule zenon_notnot_0 [OF z_Hq])
   show FALSE
   by (rule notE [OF z_Hk z_Hb])
  next
   assume z_Hr:"(~?z_hl)" (is "~(\\E x : ?z_hs(x))")
   have z_Ht: "~?z_hs(?z_hm)"
   by (rule zenon_notex_0 [of "?z_hs" "?z_hm", OF z_Hr])
   have z_Hm: "?z_hm"
   by (rule zenon_notnot_0 [OF z_Ht])
   show FALSE
   by (rule z_Hm)
  qed
 next
  assume z_Hd:"?z_hd" (is "\\E x : ?z_ho(x)")
  assume z_Hi:"?z_hi" (is "?z_hj&?z_hl")
  have z_Hu: "?z_ho((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((~(~a_CONSTANTunde_xhash_enabledhash_prime1unde_a))&(~a_CONSTANTunde_xhash_enabledhash_prime1unde_a))))" (is "?z_hw&?z_hx")
  by (rule zenon_ex_choose_0 [of "?z_ho", OF z_Hd])
  have z_Hw: "?z_hw" (is "~~?z_hv")
  by (rule zenon_and_0 [OF z_Hu])
  have z_Hx: "?z_hx"
  by (rule zenon_and_1 [OF z_Hu])
  show FALSE
  by (rule notE [OF z_Hw z_Hx])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

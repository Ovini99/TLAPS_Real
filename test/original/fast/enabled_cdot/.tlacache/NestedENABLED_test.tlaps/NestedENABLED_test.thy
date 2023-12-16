(* automatically generated -- do not edit manually *)
theory NestedENABLED_test imports Constant Zenon begin
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
fixes a_VARIABLEunde_wunde_a a_VARIABLEunde_wunde_a'
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
shows "(((((a_VARIABLEunde_zunde_a) = ((0)))) \<Rightarrow> (\<exists>a_CONSTANTunde_zhash_enabledhash_prime1unde_a : (\<exists>a_CONSTANTunde_zhash_enabledhash_prime2unde_a : (\<exists>a_CONSTANTunde_xhash_enabledhash_prime2unde_a : (\<exists>a_CONSTANTunde_whash_enabledhash_prime2unde_a : (\<exists>a_CONSTANTunde_yhash_enabledhash_prime2unde_a : ((((((((((((a_VARIABLEunde_zunde_a) = ((0)))) \<and> (((a_CONSTANTunde_zhash_enabledhash_prime2unde_a) = ((Succ[0])))))) \<and> (a_CONSTANTunde_xhash_enabledhash_prime2unde_a))) \<and> (a_CONSTANTunde_yhash_enabledhash_prime2unde_a))) \<and> (a_CONSTANTunde_whash_enabledhash_prime2unde_a))) & (((((a_CONSTANTunde_zhash_enabledhash_prime2unde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_zhash_enabledhash_prime1unde_a) = ((Succ[Succ[0]]))))))))))))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/NestedENABLED_test.tlaps/tlapm_36d1f2.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/NestedENABLED_test.tlaps/tlapm_36d1f2.znn.out
;; obligation #1
$goal (=> (= a_VARIABLEunde_zunde_a 0)
(E. ((a_CONSTANTunde_zhash_enabledhash_prime1unde_a) (E. ((a_CONSTANTunde_zhash_enabledhash_prime2unde_a) (E. ((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) (E. ((a_CONSTANTunde_whash_enabledhash_prime2unde_a) (E. ((a_CONSTANTunde_yhash_enabledhash_prime2unde_a) (/\ (/\ (/\ (/\ (/\ (= a_VARIABLEunde_zunde_a
0) (= a_CONSTANTunde_zhash_enabledhash_prime2unde_a (TLA.fapply TLA.Succ 0)))
a_CONSTANTunde_xhash_enabledhash_prime2unde_a)
a_CONSTANTunde_yhash_enabledhash_prime2unde_a)
a_CONSTANTunde_whash_enabledhash_prime2unde_a)
(/\ (= a_CONSTANTunde_zhash_enabledhash_prime2unde_a (TLA.fapply TLA.Succ 0))
(= a_CONSTANTunde_zhash_enabledhash_prime1unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((a_VARIABLEunde_zunde_a=0)=>(\\E a_CONSTANTunde_zhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_zhash_enabledhash_prime2unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime2unde_a:(\\E a_CONSTANTunde_whash_enabledhash_prime2unde_a:(\\E a_CONSTANTunde_yhash_enabledhash_prime2unde_a:((((((a_VARIABLEunde_zunde_a=0)&(a_CONSTANTunde_zhash_enabledhash_prime2unde_a=1))&a_CONSTANTunde_xhash_enabledhash_prime2unde_a)&a_CONSTANTunde_yhash_enabledhash_prime2unde_a)&a_CONSTANTunde_whash_enabledhash_prime2unde_a)&((a_CONSTANTunde_zhash_enabledhash_prime2unde_a=1)&(a_CONSTANTunde_zhash_enabledhash_prime1unde_a=2))))))))))" (is "~(?z_hc=>?z_hf)")
 have z_Hc: "?z_hc"
 by (rule zenon_notimply_0 [OF z_Ha])
 have z_Hz: "(~?z_hf)" (is "~(\\E x : ?z_hba(x))")
 by (rule zenon_notimply_1 [OF z_Ha])
 have z_Hbb: "~?z_hba(2)" (is "~(\\E x : ?z_hbc(x))")
 by (rule zenon_notex_0 [of "?z_hba" "2", OF z_Hz])
 have z_Hbd: "~?z_hbc(1)" (is "~(\\E x : ?z_hbe(x))")
 by (rule zenon_notex_0 [of "?z_hbc" "1", OF z_Hbb])
 have z_Hbf: "~?z_hbe(TRUE)" (is "~(\\E x : ?z_hbh(x))")
 by (rule zenon_notex_0 [of "?z_hbe" "TRUE", OF z_Hbd])
 have z_Hbi: "~?z_hbh(TRUE)" (is "~(\\E x : ?z_hbj(x))")
 by (rule zenon_notex_0 [of "?z_hbh" "TRUE", OF z_Hbf])
 have z_Hbk: "~?z_hbj(TRUE)" (is "~(?z_hbl&?z_hbm)")
 by (rule zenon_notex_0 [of "?z_hbj" "TRUE", OF z_Hbi])
 show FALSE
 proof (rule zenon_notand [OF z_Hbk])
  assume z_Hbn:"(~?z_hbl)" (is "~(?z_hbo&?z_hbg)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbn])
   assume z_Hbp:"(~?z_hbo)" (is "~(?z_hbq&_)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbp])
    assume z_Hbr:"(~?z_hbq)" (is "~(?z_hbs&_)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbr])
     assume z_Hbt:"(~?z_hbs)" (is "~(_&?z_hbu)")
     show FALSE
     proof (rule zenon_notand [OF z_Hbt])
      assume z_Hbv:"(a_VARIABLEunde_zunde_a~=0)"
      show FALSE
      by (rule notE [OF z_Hbv z_Hc])
     next
      assume z_Hbw:"(1~=1)" (is "?z_hr~=_")
      show FALSE
      by (rule zenon_noteq [OF z_Hbw])
     qed
    next
     assume z_Hbx:"(~?z_hbg)"
     show FALSE
     by (rule zenon_nottrue [OF z_Hbx])
    qed
   next
    assume z_Hbx:"(~?z_hbg)"
    show FALSE
    by (rule zenon_nottrue [OF z_Hbx])
   qed
  next
   assume z_Hbx:"(~?z_hbg)"
   show FALSE
   by (rule zenon_nottrue [OF z_Hbx])
  qed
 next
  assume z_Hby:"(~?z_hbm)" (is "~(?z_hbu&?z_hbz)")
  show FALSE
  proof (rule zenon_notand [OF z_Hby])
   assume z_Hbw:"(1~=1)" (is "?z_hr~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hbw])
  next
   assume z_Hca:"(2~=2)" (is "?z_hy~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hca])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
lemma ob'5:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
shows "(\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) & (\<exists>a_CONSTANTunde_yhash_enabledhash_prime2unde_a : (((a_CONSTANTunde_yhash_enabledhash_prime2unde_a) \<and> (\<exists>a_CONSTANTunde_zhash_enabledhash_prime3unde_a : (a_CONSTANTunde_zhash_enabledhash_prime3unde_a))))) & (\<exists>a_CONSTANTunde_xhash_enabledhash_prime2unde_a : (a_CONSTANTunde_xhash_enabledhash_prime2unde_a))))"(is "PROP ?ob'5")
proof -
ML_command {* writeln "*** TLAPS ENTER 5"; *}
show "PROP ?ob'5"

(* BEGIN ZENON INPUT
;; file=.tlacache/NestedENABLED_test.tlaps/tlapm_c43430.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/NestedENABLED_test.tlaps/tlapm_c43430.znn.out
;; obligation #5
$goal (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ a_CONSTANTunde_xhash_enabledhash_prime1unde_a
(E. ((a_CONSTANTunde_yhash_enabledhash_prime2unde_a) (/\ a_CONSTANTunde_yhash_enabledhash_prime2unde_a
(E. ((a_CONSTANTunde_zhash_enabledhash_prime3unde_a) a_CONSTANTunde_zhash_enabledhash_prime3unde_a)))))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) a_CONSTANTunde_xhash_enabledhash_prime2unde_a)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have zenon_L1_: "(~(\\E a_CONSTANTunde_zhash_enabledhash_prime3unde_a:a_CONSTANTunde_zhash_enabledhash_prime3unde_a)) ==> FALSE" (is "?z_hb ==> FALSE")
 proof -
  assume z_Hb:"?z_hb" (is "~(\\E x : ?z_he(x))")
  have z_Hf: "~?z_he(TRUE)" (is "~?z_hg")
  by (rule zenon_notex_0 [of "?z_he" "?z_hg", OF z_Hb])
  show FALSE
  by (rule zenon_nottrue [OF z_Hf])
 qed
 assume z_Ha:"(~(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(a_CONSTANTunde_xhash_enabledhash_prime1unde_a&((\\E a_CONSTANTunde_yhash_enabledhash_prime2unde_a:(a_CONSTANTunde_yhash_enabledhash_prime2unde_a&(\\E a_CONSTANTunde_zhash_enabledhash_prime3unde_a:a_CONSTANTunde_zhash_enabledhash_prime3unde_a)))&(\\E a_CONSTANTunde_zhash_enabledhash_prime3unde_a:a_CONSTANTunde_zhash_enabledhash_prime3unde_a)))))" (is "~(\\E x : ?z_ho(x))")
 have z_Hp: "~?z_ho(TRUE)" (is "~(?z_hg&?z_hk)")
 by (rule zenon_notex_0 [of "?z_ho" "?z_hg", OF z_Ha])
 show FALSE
 proof (rule zenon_notand [OF z_Hp])
  assume z_Hf:"(~?z_hg)"
  show FALSE
  by (rule zenon_nottrue [OF z_Hf])
 next
  assume z_Hq:"(~?z_hk)" (is "~(?z_hl&?z_hc)")
  show FALSE
  proof (rule zenon_notand [OF z_Hq])
   assume z_Hr:"(~?z_hl)" (is "~(\\E x : ?z_hs(x))")
   have z_Ht: "~?z_hs(?z_hg)"
   by (rule zenon_notex_0 [of "?z_hs" "?z_hg", OF z_Hr])
   show FALSE
   proof (rule zenon_notand [OF z_Ht])
    assume z_Hf:"(~?z_hg)"
    show FALSE
    by (rule zenon_nottrue [OF z_Hf])
   next
    assume z_Hb:"(~?z_hc)" (is "~(\\E x : ?z_he(x))")
    show FALSE
    by (rule zenon_L1_ [OF z_Hb])
   qed
  next
   assume z_Hb:"(~?z_hc)" (is "~(\\E x : ?z_he(x))")
   show FALSE
   by (rule zenon_L1_ [OF z_Hb])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 5"; *} qed
lemma ob'8:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
shows "(((((a_VARIABLEunde_xunde_a) = ((0)))) \<Rightarrow> (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (\<exists>a_CONSTANTunde_xhash_enabledhash_prime2unde_a : ((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[0])))))) & (((((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[Succ[0]])))))))))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"

(* BEGIN ZENON INPUT
;; file=.tlacache/NestedENABLED_test.tlaps/tlapm_55c8f8.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/NestedENABLED_test.tlaps/tlapm_55c8f8.znn.out
;; obligation #8
$goal (=> (= a_VARIABLEunde_xunde_a 0)
(E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (E. ((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
0) (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a (TLA.fapply TLA.Succ 0)))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a (TLA.fapply TLA.Succ 0))
(= a_CONSTANTunde_xhash_enabledhash_prime1unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((a_VARIABLEunde_xunde_a=0)=>(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime2unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime2unde_a=1))&((a_CONSTANTunde_xhash_enabledhash_prime2unde_a=1)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=2)))))))" (is "~(?z_hc=>?z_hf)")
 have z_Hc: "?z_hc"
 by (rule zenon_notimply_0 [OF z_Ha])
 have z_Hq: "(~?z_hf)" (is "~(\\E x : ?z_hr(x))")
 by (rule zenon_notimply_1 [OF z_Ha])
 have z_Hs: "~?z_hr(2)" (is "~(\\E x : ?z_ht(x))")
 by (rule zenon_notex_0 [of "?z_hr" "2", OF z_Hq])
 have z_Hu: "~?z_ht(1)" (is "~(?z_hv&?z_hw)")
 by (rule zenon_notex_0 [of "?z_ht" "1", OF z_Hs])
 show FALSE
 proof (rule zenon_notand [OF z_Hu])
  assume z_Hx:"(~?z_hv)" (is "~(_&?z_hy)")
  show FALSE
  proof (rule zenon_notand [OF z_Hx])
   assume z_Hz:"(a_VARIABLEunde_xunde_a~=0)"
   show FALSE
   by (rule notE [OF z_Hz z_Hc])
  next
   assume z_Hba:"(1~=1)" (is "?z_hl~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hba])
  qed
 next
  assume z_Hbb:"(~?z_hw)" (is "~(?z_hy&?z_hbc)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbb])
   assume z_Hba:"(1~=1)" (is "?z_hl~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hba])
  next
   assume z_Hbd:"(2~=2)" (is "?z_hp~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hbd])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
end

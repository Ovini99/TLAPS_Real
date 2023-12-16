(* automatically generated -- do not edit manually *)
theory NestedCdot_test imports Constant Zenon begin
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

lemma ob'7:
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
shows "(((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]])))))) \<Rightarrow> (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))))) & (\<exists>a_CONSTANTunde_xhash_enabledhash_prime2unde_a : ((((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[Succ[0]])))))) & (((((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[Succ[0]])))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]]))))))))))))"(is "PROP ?ob'7")
proof -
ML_command {* writeln "*** TLAPS ENTER 7"; *}
show "PROP ?ob'7"

(* BEGIN ZENON INPUT
;; file=.tlacache/NestedCdot_test.tlaps/tlapm_5cd667.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/NestedCdot_test.tlaps/tlapm_5cd667.znn.out
;; obligation #7
$goal (=> (/\ (= a_VARIABLEunde_xunde_a 0)
(= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
0) (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a (TLA.fapply TLA.Succ 0)))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) (/\ (/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a
(TLA.fapply TLA.Succ 0)) (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(((a_VARIABLEunde_xunde_a=0)&(a_VARIABLEunde_xunde_hash_primea=3))=>(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(\\E a_CONSTANTunde_xhash_enabledhash_prime2unde_a:(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)&(a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2))&((a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2)&(a_VARIABLEunde_xunde_hash_primea=3))))))))" (is "~(?z_hc=>?z_hj)")
 have z_Hc: "?z_hc" (is "?z_hd&?z_hg")
 by (rule zenon_notimply_0 [OF z_Ha])
 have z_Hw: "(~?z_hj)" (is "~(\\E x : ?z_hx(x))")
 by (rule zenon_notimply_1 [OF z_Ha])
 have z_Hd: "?z_hd"
 by (rule zenon_and_0 [OF z_Hc])
 have z_Hg: "?z_hg" (is "_=?z_hi")
 by (rule zenon_and_1 [OF z_Hc])
 have z_Hy: "~?z_hx(1)" (is "~(?z_hz&?z_hba)")
 by (rule zenon_notex_0 [of "?z_hx" "1", OF z_Hw])
 show FALSE
 proof (rule zenon_notand [OF z_Hy])
  assume z_Hbb:"(~?z_hz)" (is "~(_&?z_hbc)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbb])
   assume z_Hbd:"(a_VARIABLEunde_xunde_a~=0)"
   show FALSE
   by (rule notE [OF z_Hbd z_Hd])
  next
   assume z_Hbe:"(1~=1)" (is "?z_ho~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hbe])
  qed
 next
  assume z_Hbf:"(~?z_hba)" (is "~(\\E x : ?z_hbg(x))")
  have z_Hbh: "~?z_hbg(2)" (is "~(?z_hbi&?z_hbj)")
  by (rule zenon_notex_0 [of "?z_hbg" "2", OF z_Hbf])
  show FALSE
  proof (rule zenon_notand [OF z_Hbh])
   assume z_Hbk:"(~?z_hbi)" (is "~(?z_hbc&?z_hbl)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbk])
    assume z_Hbe:"(1~=1)" (is "?z_ho~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hbe])
   next
    assume z_Hbm:"(2~=2)" (is "?z_hu~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hbm])
   qed
  next
   assume z_Hbn:"(~?z_hbj)" (is "~(?z_hbl&_)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbn])
    assume z_Hbm:"(2~=2)" (is "?z_hu~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hbm])
   next
    assume z_Hbo:"(a_VARIABLEunde_xunde_hash_primea~=?z_hi)"
    show FALSE
    by (rule notE [OF z_Hbo z_Hg])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 7"; *} qed
lemma ob'10:
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
(* usable definition ACTION_A_ suppressed *)
(* usable definition ACTION_P_ suppressed *)
shows "(((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]])))))) \<Rightarrow> (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))))) & (\<exists>a_CONSTANTunde_xhash_enabledhash_prime2unde_a : ((((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[Succ[0]])))))) & (((((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[Succ[0]])))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]]))))))))))))"(is "PROP ?ob'10")
proof -
ML_command {* writeln "*** TLAPS ENTER 10"; *}
show "PROP ?ob'10"

(* BEGIN ZENON INPUT
;; file=.tlacache/NestedCdot_test.tlaps/tlapm_2c785b.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/NestedCdot_test.tlaps/tlapm_2c785b.znn.out
;; obligation #10
$goal (=> (/\ (= a_VARIABLEunde_xunde_a 0)
(= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
0) (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a (TLA.fapply TLA.Succ 0)))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) (/\ (/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a
(TLA.fapply TLA.Succ 0)) (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(((a_VARIABLEunde_xunde_a=0)&(a_VARIABLEunde_xunde_hash_primea=3))=>(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(\\E a_CONSTANTunde_xhash_enabledhash_prime2unde_a:(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)&(a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2))&((a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2)&(a_VARIABLEunde_xunde_hash_primea=3))))))))" (is "~(?z_hc=>?z_hj)")
 have z_Hc: "?z_hc" (is "?z_hd&?z_hg")
 by (rule zenon_notimply_0 [OF z_Ha])
 have z_Hw: "(~?z_hj)" (is "~(\\E x : ?z_hx(x))")
 by (rule zenon_notimply_1 [OF z_Ha])
 have z_Hd: "?z_hd"
 by (rule zenon_and_0 [OF z_Hc])
 have z_Hg: "?z_hg" (is "_=?z_hi")
 by (rule zenon_and_1 [OF z_Hc])
 have z_Hy: "~?z_hx(1)" (is "~(?z_hz&?z_hba)")
 by (rule zenon_notex_0 [of "?z_hx" "1", OF z_Hw])
 show FALSE
 proof (rule zenon_notand [OF z_Hy])
  assume z_Hbb:"(~?z_hz)" (is "~(_&?z_hbc)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbb])
   assume z_Hbd:"(a_VARIABLEunde_xunde_a~=0)"
   show FALSE
   by (rule notE [OF z_Hbd z_Hd])
  next
   assume z_Hbe:"(1~=1)" (is "?z_ho~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hbe])
  qed
 next
  assume z_Hbf:"(~?z_hba)" (is "~(\\E x : ?z_hbg(x))")
  have z_Hbh: "~?z_hbg(2)" (is "~(?z_hbi&?z_hbj)")
  by (rule zenon_notex_0 [of "?z_hbg" "2", OF z_Hbf])
  show FALSE
  proof (rule zenon_notand [OF z_Hbh])
   assume z_Hbk:"(~?z_hbi)" (is "~(?z_hbc&?z_hbl)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbk])
    assume z_Hbe:"(1~=1)" (is "?z_ho~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hbe])
   next
    assume z_Hbm:"(2~=2)" (is "?z_hu~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hbm])
   qed
  next
   assume z_Hbn:"(~?z_hbj)" (is "~(?z_hbl&_)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbn])
    assume z_Hbm:"(2~=2)" (is "?z_hu~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hbm])
   next
    assume z_Hbo:"(a_VARIABLEunde_xunde_hash_primea~=?z_hi)"
    show FALSE
    by (rule notE [OF z_Hbo z_Hg])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 10"; *} qed
lemma ob'4:
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
shows "(((((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))))) & (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]])))))) \<Leftrightarrow> (((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]]))))))))"(is "PROP ?ob'4")
proof -
ML_command {* writeln "*** TLAPS ENTER 4"; *}
show "PROP ?ob'4"

(* BEGIN ZENON INPUT
;; file=.tlacache/NestedCdot_test.tlaps/tlapm_4a0e2a.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/NestedCdot_test.tlaps/tlapm_4a0e2a.znn.out
;; obligation #4
$goal (<=> (/\ (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
0) (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a (TLA.fapply TLA.Succ 0)))
(= a_CONSTANTunde_xhash_enabledhash_prime1unde_a (TLA.fapply TLA.Succ 0)))))
(= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(/\ (= a_VARIABLEunde_xunde_a 0) (= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)))&(a_VARIABLEunde_xunde_hash_primea=3))<=>((a_VARIABLEunde_xunde_a=0)&(a_VARIABLEunde_xunde_hash_primea=3))))" (is "~(?z_hc<=>?z_hp)")
 show FALSE
 proof (rule zenon_notequiv [OF z_Ha])
  assume z_Hq:"(~?z_hc)" (is "~(?z_hd&?z_hm)")
  assume z_Hp:"?z_hp" (is "?z_hg&_")
  have z_Hg: "?z_hg"
  by (rule zenon_and_0 [OF z_Hp])
  have z_Hm: "?z_hm" (is "_=?z_ho")
  by (rule zenon_and_1 [OF z_Hp])
  show FALSE
  proof (rule zenon_notand [OF z_Hq])
   assume z_Hr:"(~?z_hd)" (is "~(\\E x : ?z_hs(x))")
   have z_Ht: "~?z_hs(1)" (is "~(?z_hu&?z_hv)")
   by (rule zenon_notex_0 [of "?z_hs" "1", OF z_Hr])
   show FALSE
   proof (rule zenon_notand [OF z_Ht])
    assume z_Hw:"(~?z_hu)"
    show FALSE
    proof (rule zenon_notand [OF z_Hw])
     assume z_Hx:"(a_VARIABLEunde_xunde_a~=0)"
     show FALSE
     by (rule notE [OF z_Hx z_Hg])
    next
     assume z_Hy:"(1~=1)" (is "?z_hl~=_")
     show FALSE
     by (rule zenon_noteq [OF z_Hy])
    qed
   next
    assume z_Hy:"(1~=1)" (is "?z_hl~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hy])
   qed
  next
   assume z_Hz:"(a_VARIABLEunde_xunde_hash_primea~=?z_ho)"
   show FALSE
   by (rule notE [OF z_Hz z_Hm])
  qed
 next
  assume z_Hc:"?z_hc" (is "?z_hd&?z_hm")
  assume z_Hba:"(~?z_hp)" (is "~(?z_hg&_)")
  have z_Hd: "?z_hd" (is "\\E x : ?z_hs(x)")
  by (rule zenon_and_0 [OF z_Hc])
  have z_Hm: "?z_hm" (is "_=?z_ho")
  by (rule zenon_and_1 [OF z_Hc])
  have z_Hbb: "?z_hs((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))))" (is "?z_hbd&?z_hbe")
  by (rule zenon_ex_choose_0 [of "?z_hs", OF z_Hd])
  have z_Hbd: "?z_hbd"
  by (rule zenon_and_0 [OF z_Hbb])
  have z_Hg: "?z_hg"
  by (rule zenon_and_0 [OF z_Hbd])
  show FALSE
  proof (rule zenon_notand [OF z_Hba])
   assume z_Hx:"(a_VARIABLEunde_xunde_a~=0)"
   show FALSE
   by (rule notE [OF z_Hx z_Hg])
  next
   assume z_Hz:"(a_VARIABLEunde_xunde_hash_primea~=?z_ho)"
   show FALSE
   by (rule notE [OF z_Hz z_Hm])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 4"; *} qed
lemma ob'1:
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
shows "(((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))))) & (\<exists>a_CONSTANTunde_xhash_enabledhash_prime2unde_a : ((((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[Succ[0]])))))) & (((((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) = ((Succ[Succ[0]])))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]])))))))))) = (((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : ((((((a_VARIABLEunde_xunde_a) = ((0)))) \<and> (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))))) & (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = ((Succ[0])))))) \<and> ((((a_VARIABLEunde_xunde_hash_primea :: c)) = ((Succ[Succ[Succ[0]]]))))))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/NestedCdot_test.tlaps/tlapm_e4da87.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/NestedCdot_test.tlaps/tlapm_e4da87.znn.out
;; obligation #1
$goal (= (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
0) (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a (TLA.fapply TLA.Succ 0)))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime2unde_a) (/\ (/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a
(TLA.fapply TLA.Succ 0)) (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime2unde_a
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(/\ (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
0) (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a (TLA.fapply TLA.Succ 0)))
(= a_CONSTANTunde_xhash_enabledhash_prime1unde_a (TLA.fapply TLA.Succ 0)))))
(= a_VARIABLEunde_xunde_hash_primea
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(\\E a_CONSTANTunde_xhash_enabledhash_prime2unde_a:(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)&(a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2))&((a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2)&(a_VARIABLEunde_xunde_hash_primea=3))))))~=((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)))&(a_VARIABLEunde_xunde_hash_primea=3)))" (is "?z_hb~=?z_hu")
 show FALSE
 proof (rule zenon_boolcase_ex [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hu))" "(\<lambda>a_CONSTANTunde_xhash_enabledhash_prime1unde_a. (((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(\\E a_CONSTANTunde_xhash_enabledhash_prime2unde_a:(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)&(a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2))&((a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2)&(a_VARIABLEunde_xunde_hash_primea=3))))))", OF z_Ha])
  assume z_Hbb:"(?z_hb=TRUE)" (is "_=?z_hbc")
  assume z_Hbd:"(?z_hbc~=?z_hu)"
  have z_Hb: "?z_hb" (is "\\E x : ?z_hba(x)")
  by (rule zenon_eq_x_true_0 [of "?z_hb", OF z_Hbb])
  have z_Hbe: "?z_hba((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(\\E a_CONSTANTunde_xhash_enabledhash_prime2unde_a:(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)&(a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2))&((a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2)&(a_VARIABLEunde_xunde_hash_primea=3)))))))" (is "?z_hbg&?z_hbh")
  by (rule zenon_ex_choose_0 [of "?z_hba", OF z_Hb])
  have z_Hbg: "?z_hbg" (is "?z_he&?z_hbi")
  by (rule zenon_and_0 [OF z_Hbe])
  have z_Hbh: "?z_hbh" (is "\\E x : ?z_hbj(x)")
  by (rule zenon_and_1 [OF z_Hbe])
  have z_He: "?z_he"
  by (rule zenon_and_0 [OF z_Hbg])
  have z_Hbk: "?z_hbj((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime2unde_a:((?z_hbi&(a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2))&((a_CONSTANTunde_xhash_enabledhash_prime2unde_a=2)&(a_VARIABLEunde_xunde_hash_primea=3)))))" (is "?z_hbo&?z_hbp")
  by (rule zenon_ex_choose_0 [of "?z_hbj", OF z_Hbh])
  have z_Hbo: "?z_hbo" (is "_&?z_hbq")
  by (rule zenon_and_0 [OF z_Hbk])
  have z_Hbp: "?z_hbp" (is "_&?z_hr")
  by (rule zenon_and_1 [OF z_Hbk])
  have z_Hr: "?z_hr" (is "_=?z_ht")
  by (rule zenon_and_1 [OF z_Hbp])
  have z_Hbi: "?z_hbi" (is "?z_hbf=?z_hj")
  by (rule zenon_and_0 [OF z_Hbo])
  have z_Hbr: "(~?z_hu)" (is "~(?z_hv&_)")
  by (rule zenon_noteq_true_x_0 [of "?z_hu", OF z_Hbd])
  show FALSE
  proof (rule zenon_notand [OF z_Hbr])
   assume z_Hbs:"(~?z_hv)" (is "~(\\E x : ?z_hbt(x))")
   have z_Hbu: "~?z_hbt(?z_hbf)"
   by (rule zenon_notex_0 [of "?z_hbt" "?z_hbf", OF z_Hbs])
   show FALSE
   proof (rule zenon_notand [OF z_Hbu])
    assume z_Hbv:"(~?z_hbg)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbv])
     assume z_Hbw:"(a_VARIABLEunde_xunde_a~=0)"
     show FALSE
     by (rule notE [OF z_Hbw z_He])
    next
     assume z_Hbx:"(?z_hbf~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hbx z_Hbi])
    qed
   next
    assume z_Hbx:"(?z_hbf~=?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbx z_Hbi])
   qed
  next
   assume z_Hby:"(a_VARIABLEunde_xunde_hash_primea~=?z_ht)"
   show FALSE
   by (rule notE [OF z_Hby z_Hr])
  qed
 next
  assume z_Hbz:"(?z_hb=FALSE)" (is "_=?z_hca")
  assume z_Hcb:"(?z_hca~=?z_hu)"
  have z_Hcc: "(~?z_hb)" (is "~(\\E x : ?z_hba(x))")
  by (rule zenon_eq_x_false_0 [of "?z_hb", OF z_Hbz])
  show FALSE
  proof (rule zenon_boolcase_and [of "(\<lambda>zenon_Vg. (?z_hca~=zenon_Vg))" "(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1)))" "(a_VARIABLEunde_xunde_hash_primea=3)", OF z_Hcb])
   assume z_Hcg:"(?z_hu=TRUE)" (is "_=?z_hbc")
   assume z_Hch:"(?z_hca~=?z_hbc)"
   have z_Hu: "?z_hu" (is "?z_hv&?z_hr")
   by (rule zenon_eq_x_true_0 [of "?z_hu", OF z_Hcg])
   have z_Hv: "?z_hv" (is "\\E x : ?z_hbt(x)")
   by (rule zenon_and_0 [OF z_Hu])
   have z_Hr: "?z_hr" (is "_=?z_ht")
   by (rule zenon_and_1 [OF z_Hu])
   have z_Hci: "?z_hbt((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=0)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=1))))" (is "?z_hck&?z_hcl")
   by (rule zenon_ex_choose_0 [of "?z_hbt", OF z_Hv])
   have z_Hck: "?z_hck" (is "?z_he&_")
   by (rule zenon_and_0 [OF z_Hci])
   have z_He: "?z_he"
   by (rule zenon_and_0 [OF z_Hck])
   have z_Hcl: "?z_hcl" (is "?z_hcj=?z_hj")
   by (rule zenon_and_1 [OF z_Hck])
   have z_Hcm: "~?z_hba(?z_hcj)" (is "~(_&?z_hcn)")
   by (rule zenon_notex_0 [of "?z_hba" "?z_hcj", OF z_Hcc])
   show FALSE
   proof (rule zenon_notand [OF z_Hcm])
    assume z_Hco:"(~?z_hck)"
    show FALSE
    proof (rule zenon_notand [OF z_Hco])
     assume z_Hbw:"(a_VARIABLEunde_xunde_a~=0)"
     show FALSE
     by (rule notE [OF z_Hbw z_He])
    next
     assume z_Hcp:"(?z_hcj~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hcp z_Hcl])
    qed
   next
    assume z_Hcq:"(~?z_hcn)" (is "~(\\E x : ?z_hcr(x))")
    have z_Hcs: "~?z_hcr(2)" (is "~(?z_hct&?z_hcu)")
    by (rule zenon_notex_0 [of "?z_hcr" "2", OF z_Hcq])
    show FALSE
    proof (rule zenon_notand [OF z_Hcs])
     assume z_Hcv:"(~?z_hct)" (is "~(_&?z_hcw)")
     show FALSE
     proof (rule zenon_notand [OF z_Hcv])
      assume z_Hcp:"(?z_hcj~=?z_hj)"
      show FALSE
      by (rule notE [OF z_Hcp z_Hcl])
     next
      assume z_Hcx:"(2~=2)" (is "?z_hp~=_")
      show FALSE
      by (rule zenon_noteq [OF z_Hcx])
     qed
    next
     assume z_Hcy:"(~?z_hcu)" (is "~(?z_hcw&_)")
     show FALSE
     proof (rule zenon_notand [OF z_Hcy])
      assume z_Hcx:"(2~=2)" (is "?z_hp~=_")
      show FALSE
      by (rule zenon_noteq [OF z_Hcx])
     next
      assume z_Hby:"(a_VARIABLEunde_xunde_hash_primea~=?z_ht)"
      show FALSE
      by (rule notE [OF z_Hby z_Hr])
     qed
    qed
   qed
  next
   assume z_Hcz:"(?z_hu=?z_hca)"
   assume z_Hda:"(?z_hca~=?z_hca)"
   show FALSE
   by (rule zenon_eqsym [OF z_Hcz z_Hcb])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

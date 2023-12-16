(* automatically generated -- do not edit manually *)
theory Subref_test imports Constant Zenon begin
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

lemma ob'6:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
shows "(((((((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a))) \<and> (((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a))))) \<and> ((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))))"(is "PROP ?ob'6")
proof -
ML_command {* writeln "*** TLAPS ENTER 6"; *}
show "PROP ?ob'6"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_b19243.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_b19243.znn.out
;; obligation #6
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$goal (/\ (/\ (= a_CONSTANTunde_Sunde_a a_CONSTANTunde_Sunde_a)
(= a_CONSTANTunde_Tunde_a a_CONSTANTunde_Tunde_a))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hk:"(~(((a_CONSTANTunde_Sunde_a=a_CONSTANTunde_Sunde_a)&(a_CONSTANTunde_Tunde_a=a_CONSTANTunde_Tunde_a))&(3=3)))" (is "~(?z_hm&?z_hp)")
 show FALSE
 proof (rule zenon_notand [OF z_Hk])
  assume z_Hr:"(~?z_hm)" (is "~(?z_hf&?z_hg)")
  show FALSE
  proof (rule zenon_notand [OF z_Hr])
   assume z_Hs:"(a_CONSTANTunde_Sunde_a~=a_CONSTANTunde_Sunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hs])
  next
   assume z_Ht:"(a_CONSTANTunde_Tunde_a~=a_CONSTANTunde_Tunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Ht])
  qed
 next
  assume z_Hu:"(3~=3)" (is "?z_hq~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hu])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 6"; *} qed
lemma ob'5:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
shows "(((((((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a))) \<and> (((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a))))) \<and> ((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))))"(is "PROP ?ob'5")
proof -
ML_command {* writeln "*** TLAPS ENTER 5"; *}
show "PROP ?ob'5"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_3de842.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_3de842.znn.out
;; obligation #5
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$goal (/\ (/\ (= a_CONSTANTunde_Sunde_a a_CONSTANTunde_Sunde_a)
(= a_CONSTANTunde_Tunde_a a_CONSTANTunde_Tunde_a))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hj:"(~(((a_CONSTANTunde_Sunde_a=a_CONSTANTunde_Sunde_a)&(a_CONSTANTunde_Tunde_a=a_CONSTANTunde_Tunde_a))&(2=2)))" (is "~(?z_hl&?z_ho)")
 show FALSE
 proof (rule zenon_notand [OF z_Hj])
  assume z_Hq:"(~?z_hl)" (is "~(?z_hf&?z_hg)")
  show FALSE
  proof (rule zenon_notand [OF z_Hq])
   assume z_Hr:"(a_CONSTANTunde_Sunde_a~=a_CONSTANTunde_Sunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hr])
  next
   assume z_Hs:"(a_CONSTANTunde_Tunde_a~=a_CONSTANTunde_Tunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hs])
  qed
 next
  assume z_Ht:"(2~=2)" (is "?z_hp~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Ht])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 5"; *} qed
lemma ob'4:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
shows "(((((((((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a))) \<and> (((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a))))) \<and> (((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a))))) \<and> ((((Succ[0])) = ((Succ[0]))))))"(is "PROP ?ob'4")
proof -
ML_command {* writeln "*** TLAPS ENTER 4"; *}
show "PROP ?ob'4"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_30b640.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_30b640.znn.out
;; obligation #4
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$goal (/\ (/\ (/\ (= a_CONSTANTunde_Sunde_a a_CONSTANTunde_Sunde_a)
(= a_CONSTANTunde_Tunde_a a_CONSTANTunde_Tunde_a)) (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)) (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hf:"(~((((a_CONSTANTunde_Sunde_a=a_CONSTANTunde_Sunde_a)&(a_CONSTANTunde_Tunde_a=a_CONSTANTunde_Tunde_a))&(a_CONSTANTunde_Uunde_a=a_CONSTANTunde_Uunde_a))&(1=1)))" (is "~(?z_hh&?z_hp)")
 show FALSE
 proof (rule zenon_notand [OF z_Hf])
  assume z_Hr:"(~?z_hh)" (is "~(?z_hi&?z_hn)")
  show FALSE
  proof (rule zenon_notand [OF z_Hr])
   assume z_Hs:"(~?z_hi)" (is "~(?z_hj&?z_hl)")
   show FALSE
   proof (rule zenon_notand [OF z_Hs])
    assume z_Ht:"(a_CONSTANTunde_Sunde_a~=a_CONSTANTunde_Sunde_a)"
    show FALSE
    by (rule zenon_noteq [OF z_Ht])
   next
    assume z_Hu:"(a_CONSTANTunde_Tunde_a~=a_CONSTANTunde_Tunde_a)"
    show FALSE
    by (rule zenon_noteq [OF z_Hu])
   qed
  next
   assume z_Hv:"(a_CONSTANTunde_Uunde_a~=a_CONSTANTunde_Uunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hv])
  qed
 next
  assume z_Hw:"(1~=1)" (is "?z_hq~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hw])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 4"; *} qed
lemma ob'7:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'30: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'31: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'32: "((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))"
shows "((((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))) = ((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))))) \<and> ((((Succ[Succ[Succ[Succ[0]]]])) = ((Succ[Succ[Succ[Succ[0]]]]))))))"(is "PROP ?ob'7")
proof -
ML_command {* writeln "*** TLAPS ENTER 7"; *}
show "PROP ?ob'7"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_4f2281.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_4f2281.znn.out
;; obligation #7
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'30" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'31" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'32" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
$goal (/\ (= (/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a))
(/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a)))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hl:"(~((((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))&a_CONSTANTunde_Runde_a(a_CONSTANTunde_junde_a, a_CONSTANTunde_kunde_a, a_CONSTANTunde_lunde_a))=((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))&a_CONSTANTunde_Runde_a(a_CONSTANTunde_junde_a, a_CONSTANTunde_kunde_a, a_CONSTANTunde_lunde_a)))&(4=4)))" (is "~(?z_hn&?z_hz)")
 show FALSE
 proof (rule zenon_notand [OF z_Hl])
  assume z_Hbb:"(((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))&a_CONSTANTunde_Runde_a(a_CONSTANTunde_junde_a, a_CONSTANTunde_kunde_a, a_CONSTANTunde_lunde_a))~=((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))&a_CONSTANTunde_Runde_a(a_CONSTANTunde_junde_a, a_CONSTANTunde_kunde_a, a_CONSTANTunde_lunde_a)))" (is "?z_ho~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbb])
 next
  assume z_Hbc:"(4~=4)" (is "?z_hba~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbc])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 7"; *} qed
lemma ob'3:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
shows "((((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a))) & (((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a))) & (((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a))))"(is "PROP ?ob'3")
proof -
ML_command {* writeln "*** TLAPS ENTER 3"; *}
show "PROP ?ob'3"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_155561.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_155561.znn.out
;; obligation #3
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$goal (/\ (= a_CONSTANTunde_junde_a a_CONSTANTunde_junde_a)
(= a_CONSTANTunde_kunde_a a_CONSTANTunde_kunde_a) (= a_CONSTANTunde_lunde_a
a_CONSTANTunde_lunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_He:"(~((a_CONSTANTunde_junde_a=a_CONSTANTunde_junde_a)&((a_CONSTANTunde_kunde_a=a_CONSTANTunde_kunde_a)&(a_CONSTANTunde_lunde_a=a_CONSTANTunde_lunde_a))))" (is "~(?z_hg&?z_hi)")
 show FALSE
 proof (rule zenon_notand [OF z_He])
  assume z_Hn:"(a_CONSTANTunde_junde_a~=a_CONSTANTunde_junde_a)"
  show FALSE
  by (rule zenon_noteq [OF z_Hn])
 next
  assume z_Ho:"(~?z_hi)" (is "~(?z_hj&?z_hl)")
  show FALSE
  proof (rule zenon_notand [OF z_Ho])
   assume z_Hp:"(a_CONSTANTunde_kunde_a~=a_CONSTANTunde_kunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hp])
  next
   assume z_Hq:"(a_CONSTANTunde_lunde_a~=a_CONSTANTunde_lunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hq])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 3"; *} qed
lemma ob'8:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'30: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'31: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'32: "((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))"
assumes v'33: "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))) = ((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a))))))))"
assumes v'34: "((((Succ[Succ[Succ[Succ[0]]]])) = ((Succ[Succ[Succ[Succ[0]]]]))))"
shows "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))))) \<and> ((((Succ[Succ[Succ[Succ[Succ[0]]]]])) = ((Succ[Succ[Succ[Succ[Succ[0]]]]]))))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_4897ab.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_4897ab.znn.out
;; obligation #8
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'30" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'31" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'32" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
$hyp "v'33" (= (/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a))
(/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a)))
$hyp "v'34" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
$goal (/\ (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a)))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hn:"(~(((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))=(a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a)))&(5=5)))" (is "~(?z_hp&?z_hw)")
 show FALSE
 proof (rule zenon_notand [OF z_Hn])
  assume z_Hy:"((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))~=(a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Qunde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a)))" (is "?z_hq~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hy])
 next
  assume z_Hz:"(5~=5)" (is "?z_hx~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hz])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
lemma ob'10:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'30: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'31: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'32: "((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))"
assumes v'33: "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))) = ((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a))))))))"
assumes v'34: "((((Succ[Succ[Succ[Succ[0]]]])) = ((Succ[Succ[Succ[Succ[0]]]]))))"
assumes v'35: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a))))))))"
assumes v'36: "((((Succ[Succ[Succ[Succ[Succ[0]]]]])) = ((Succ[Succ[Succ[Succ[Succ[0]]]]]))))"
assumes v'37: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a))))))))"
assumes v'38: "((((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]))))"
shows "(((((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a))) \<and> ((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]))))))"(is "PROP ?ob'10")
proof -
ML_command {* writeln "*** TLAPS ENTER 10"; *}
show "PROP ?ob'10"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_49388d.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_49388d.znn.out
;; obligation #10
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'30" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'31" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'32" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
$hyp "v'33" (= (/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a))
(/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a)))
$hyp "v'34" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
$hyp "v'35" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a
a_CONSTANTunde_zunde_a)))
$hyp "v'36" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
$hyp "v'37" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)) (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)))
$hyp "v'38" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
$goal (/\ (= a_CONSTANTunde_Sunde_a a_CONSTANTunde_Sunde_a)
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hr:"(~((a_CONSTANTunde_Sunde_a=a_CONSTANTunde_Sunde_a)&(7=7)))" (is "~(?z_hf&?z_hu)")
 show FALSE
 proof (rule zenon_notand [OF z_Hr])
  assume z_Hw:"(a_CONSTANTunde_Sunde_a~=a_CONSTANTunde_Sunde_a)"
  show FALSE
  by (rule zenon_noteq [OF z_Hw])
 next
  assume z_Hx:"(7~=7)" (is "?z_hv~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hx])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 10"; *} qed
lemma ob'11:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'30: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'31: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'32: "((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))"
assumes v'33: "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))) = ((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a))))))))"
assumes v'34: "((((Succ[Succ[Succ[Succ[0]]]])) = ((Succ[Succ[Succ[Succ[0]]]]))))"
assumes v'35: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a))))))))"
assumes v'36: "((((Succ[Succ[Succ[Succ[Succ[0]]]]])) = ((Succ[Succ[Succ[Succ[Succ[0]]]]]))))"
assumes v'37: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a))))))))"
assumes v'38: "((((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]))))"
assumes v'39: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'40: "((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]))))"
shows "(((((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a))) \<and> ((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]))))))"(is "PROP ?ob'11")
proof -
ML_command {* writeln "*** TLAPS ENTER 11"; *}
show "PROP ?ob'11"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_893528.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_893528.znn.out
;; obligation #11
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'30" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'31" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'32" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
$hyp "v'33" (= (/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a))
(/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a)))
$hyp "v'34" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
$hyp "v'35" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a
a_CONSTANTunde_zunde_a)))
$hyp "v'36" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
$hyp "v'37" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)) (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)))
$hyp "v'38" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
$hyp "v'39" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'40" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))
$goal (/\ (= a_CONSTANTunde_Sunde_a a_CONSTANTunde_Sunde_a)
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hs:"(~((a_CONSTANTunde_Sunde_a=a_CONSTANTunde_Sunde_a)&(8=8)))" (is "~(?z_hf&?z_hv)")
 show FALSE
 proof (rule zenon_notand [OF z_Hs])
  assume z_Hx:"(a_CONSTANTunde_Sunde_a~=a_CONSTANTunde_Sunde_a)"
  show FALSE
  by (rule zenon_noteq [OF z_Hx])
 next
  assume z_Hy:"(8~=8)" (is "?z_hw~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hy])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 11"; *} qed
lemma ob'9:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'30: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'31: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'32: "((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))"
assumes v'33: "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))) = ((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a))))))))"
assumes v'34: "((((Succ[Succ[Succ[Succ[0]]]])) = ((Succ[Succ[Succ[Succ[0]]]]))))"
assumes v'35: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a))))))))"
assumes v'36: "((((Succ[Succ[Succ[Succ[Succ[0]]]]])) = ((Succ[Succ[Succ[Succ[Succ[0]]]]]))))"
shows "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))))) \<and> ((((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]))))))"(is "PROP ?ob'9")
proof -
ML_command {* writeln "*** TLAPS ENTER 9"; *}
show "PROP ?ob'9"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_63712d.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_63712d.znn.out
;; obligation #9
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'30" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'31" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'32" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
$hyp "v'33" (= (/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a))
(/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a)))
$hyp "v'34" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
$hyp "v'35" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a
a_CONSTANTunde_zunde_a)))
$hyp "v'36" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
$goal (/\ (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)) (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hp:"(~(((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Runde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a, a_CONSTANTunde_junde_a))=(a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Runde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a, a_CONSTANTunde_junde_a)))&(6=6)))" (is "~(?z_hr&?z_hz)")
 show FALSE
 proof (rule zenon_notand [OF z_Hp])
  assume z_Hbb:"((a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Runde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a, a_CONSTANTunde_junde_a))~=(a_CONSTANTunde_Punde_a(a_CONSTANTunde_xunde_a)&a_CONSTANTunde_Runde_a(a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a, a_CONSTANTunde_junde_a)))" (is "?z_hs~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbb])
 next
  assume z_Hbc:"(6~=6)" (is "?z_hba~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbc])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 9"; *} qed
lemma ob'12:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'30: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'31: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'32: "((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))"
assumes v'33: "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))) = ((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a))))))))"
assumes v'34: "((((Succ[Succ[Succ[Succ[0]]]])) = ((Succ[Succ[Succ[Succ[0]]]]))))"
assumes v'35: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a))))))))"
assumes v'36: "((((Succ[Succ[Succ[Succ[Succ[0]]]]])) = ((Succ[Succ[Succ[Succ[Succ[0]]]]]))))"
assumes v'37: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a))))))))"
assumes v'38: "((((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]))))"
assumes v'39: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'40: "((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]))))"
assumes v'41: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'42: "((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]))))"
shows "((((((a_CONSTANTunde_Punde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))) = ((a_CONSTANTunde_Punde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))))) \<and> ((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]))))))"(is "PROP ?ob'12")
proof -
ML_command {* writeln "*** TLAPS ENTER 12"; *}
show "PROP ?ob'12"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_dd19e9.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_dd19e9.znn.out
;; obligation #12
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'30" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'31" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'32" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
$hyp "v'33" (= (/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a))
(/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a)))
$hyp "v'34" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
$hyp "v'35" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a
a_CONSTANTunde_zunde_a)))
$hyp "v'36" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
$hyp "v'37" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)) (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)))
$hyp "v'38" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
$hyp "v'39" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'40" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))
$hyp "v'41" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'42" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))
$goal (/\ (= (a_CONSTANTunde_Punde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_Punde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ht:"(~((a_CONSTANTunde_Punde_a(10)=a_CONSTANTunde_Punde_a(10))&(9=9)))" (is "~(?z_hv&?z_hy)")
 show FALSE
 proof (rule zenon_notand [OF z_Ht])
  assume z_Hba:"(a_CONSTANTunde_Punde_a(10)~=a_CONSTANTunde_Punde_a(10))" (is "?z_hw~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hba])
 next
  assume z_Hbb:"(9~=9)" (is "?z_hz~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbb])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 12"; *} qed
lemma ob'13:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'23: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'24: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'25: "(((a_CONSTANTunde_Uunde_a) = (a_CONSTANTunde_Uunde_a)))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'28: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'29: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'30: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'31: "(((a_CONSTANTunde_Tunde_a) = (a_CONSTANTunde_Tunde_a)))"
assumes v'32: "((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))"
assumes v'33: "((((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a)))))) = ((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_kunde_a), (a_CONSTANTunde_lunde_a))))))))"
assumes v'34: "((((Succ[Succ[Succ[Succ[0]]]])) = ((Succ[Succ[Succ[Succ[0]]]]))))"
assumes v'35: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Qunde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a))))))))"
assumes v'36: "((((Succ[Succ[Succ[Succ[Succ[0]]]]])) = ((Succ[Succ[Succ[Succ[Succ[0]]]]]))))"
assumes v'37: "((((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))) = ((((a_CONSTANTunde_Punde_a ((a_CONSTANTunde_xunde_a)))) \<and> ((a_CONSTANTunde_Runde_a ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a))))))))"
assumes v'38: "((((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]))))"
assumes v'39: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'40: "((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]))))"
assumes v'41: "(((a_CONSTANTunde_Sunde_a) = (a_CONSTANTunde_Sunde_a)))"
assumes v'42: "((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]))))"
assumes v'43: "((((a_CONSTANTunde_Punde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))) = ((a_CONSTANTunde_Punde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]])))))))"
assumes v'44: "((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]))))"
shows "((((((a_CONSTANTunde_Punde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))) = ((a_CONSTANTunde_Punde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))))) \<and> ((((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]])) = ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))))"(is "PROP ?ob'13")
proof -
ML_command {* writeln "*** TLAPS ENTER 13"; *}
show "PROP ?ob'13"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_200f1f.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_200f1f.znn.out
;; obligation #13
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'23" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'24" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'25" (= a_CONSTANTunde_Uunde_a
a_CONSTANTunde_Uunde_a)
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'28" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'29" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'30" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'31" (= a_CONSTANTunde_Tunde_a
a_CONSTANTunde_Tunde_a)
$hyp "v'32" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
$hyp "v'33" (= (/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a))
(/\ (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Runde_a a_CONSTANTunde_junde_a a_CONSTANTunde_kunde_a
a_CONSTANTunde_lunde_a)))
$hyp "v'34" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
$hyp "v'35" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
(/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Qunde_a a_CONSTANTunde_yunde_a
a_CONSTANTunde_zunde_a)))
$hyp "v'36" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
$hyp "v'37" (= (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)) (/\ (a_CONSTANTunde_Punde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_Runde_a a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)))
$hyp "v'38" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
$hyp "v'39" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'40" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))
$hyp "v'41" (= a_CONSTANTunde_Sunde_a
a_CONSTANTunde_Sunde_a)
$hyp "v'42" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))
$hyp "v'43" (= (a_CONSTANTunde_Punde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_Punde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
$hyp "v'44" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))
$goal (/\ (= (a_CONSTANTunde_Punde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_Punde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hv:"(~((a_CONSTANTunde_Punde_a(10)=a_CONSTANTunde_Punde_a(10))&(10=10)))" (is "~(?z_ht&?z_hz)")
 show FALSE
 proof (rule zenon_notand [OF z_Hv])
  assume z_Hba:"(a_CONSTANTunde_Punde_a(10)~=a_CONSTANTunde_Punde_a(10))" (is "?z_hx~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hba])
 next
  assume z_Hbb:"(10~=10)" (is "?z_hy~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbb])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 13"; *} qed
lemma ob'15:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
assumes v'24: "(((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))"
assumes v'25: "(((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a)))"
assumes v'26: "(((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a)))"
assumes v'27: "(((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a)))"
assumes v'28: "(((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a)))"
assumes v'29: "(((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a)))"
assumes v'30: "((((0)) = ((0))))"
shows "(((((((((((((((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a))) \<and> (((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a))))) \<and> (((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a))))) \<and> (((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a))))) \<and> (((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a))))) \<and> (((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a))))) \<and> ((((Succ[0])) = ((Succ[0]))))))"(is "PROP ?ob'15")
proof -
ML_command {* writeln "*** TLAPS ENTER 15"; *}
show "PROP ?ob'15"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_576108.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_576108.znn.out
;; obligation #15
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$hyp "v'24" (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)
$hyp "v'25" (= a_CONSTANTunde_yunde_a
a_CONSTANTunde_yunde_a)
$hyp "v'26" (= a_CONSTANTunde_zunde_a
a_CONSTANTunde_zunde_a)
$hyp "v'27" (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)
$hyp "v'28" (= a_CONSTANTunde_kunde_a
a_CONSTANTunde_kunde_a)
$hyp "v'29" (= a_CONSTANTunde_lunde_a a_CONSTANTunde_lunde_a)
$hyp "v'30" (= 0 0)
$goal (/\ (/\ (/\ (/\ (/\ (/\ (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_yunde_a a_CONSTANTunde_yunde_a))
(= a_CONSTANTunde_zunde_a a_CONSTANTunde_zunde_a)) (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)) (= a_CONSTANTunde_kunde_a a_CONSTANTunde_kunde_a))
(= a_CONSTANTunde_lunde_a a_CONSTANTunde_lunde_a)) (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hn:"(~(((((((a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a)&(a_CONSTANTunde_yunde_a=a_CONSTANTunde_yunde_a))&(a_CONSTANTunde_zunde_a=a_CONSTANTunde_zunde_a))&(a_CONSTANTunde_junde_a=a_CONSTANTunde_junde_a))&(a_CONSTANTunde_kunde_a=a_CONSTANTunde_kunde_a))&(a_CONSTANTunde_lunde_a=a_CONSTANTunde_lunde_a))&(1=1)))" (is "~(?z_hp&?z_hba)")
 show FALSE
 proof (rule zenon_notand [OF z_Hn])
  assume z_Hbc:"(~?z_hp)" (is "~(?z_hq&?z_hl)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbc])
   assume z_Hbd:"(~?z_hq)" (is "~(?z_hr&?z_hk)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbd])
    assume z_Hbe:"(~?z_hr)" (is "~(?z_hs&?z_hj)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbe])
     assume z_Hbf:"(~?z_hs)" (is "~(?z_ht&?z_hi)")
     show FALSE
     proof (rule zenon_notand [OF z_Hbf])
      assume z_Hbg:"(~?z_ht)" (is "~(?z_hg&?z_hh)")
      show FALSE
      proof (rule zenon_notand [OF z_Hbg])
       assume z_Hbh:"(a_CONSTANTunde_xunde_a~=a_CONSTANTunde_xunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbh])
      next
       assume z_Hbi:"(a_CONSTANTunde_yunde_a~=a_CONSTANTunde_yunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbi])
      qed
     next
      assume z_Hbj:"(a_CONSTANTunde_zunde_a~=a_CONSTANTunde_zunde_a)"
      show FALSE
      by (rule zenon_noteq [OF z_Hbj])
     qed
    next
     assume z_Hbk:"(a_CONSTANTunde_junde_a~=a_CONSTANTunde_junde_a)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbk])
    qed
   next
    assume z_Hbl:"(a_CONSTANTunde_kunde_a~=a_CONSTANTunde_kunde_a)"
    show FALSE
    by (rule zenon_noteq [OF z_Hbl])
   qed
  next
   assume z_Hbm:"(a_CONSTANTunde_lunde_a~=a_CONSTANTunde_lunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hbm])
  qed
 next
  assume z_Hbn:"(1~=1)" (is "?z_hbb~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbn])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 15"; *} qed
lemma ob'16:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
assumes v'24: "(((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))"
assumes v'25: "(((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a)))"
assumes v'26: "(((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a)))"
assumes v'27: "(((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a)))"
assumes v'28: "(((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a)))"
assumes v'29: "(((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a)))"
assumes v'30: "((((0)) = ((0))))"
assumes v'31: "(((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))"
assumes v'32: "(((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a)))"
assumes v'33: "(((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a)))"
assumes v'34: "(((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a)))"
assumes v'35: "(((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a)))"
assumes v'36: "(((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a)))"
assumes v'37: "((((Succ[0])) = ((Succ[0]))))"
shows "(((((((((((((((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a))) \<and> (((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a))))) \<and> (((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a))))) \<and> (((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a))))) \<and> (((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a))))) \<and> (((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a))))) \<and> ((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))))"(is "PROP ?ob'16")
proof -
ML_command {* writeln "*** TLAPS ENTER 16"; *}
show "PROP ?ob'16"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_5bb14d.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_5bb14d.znn.out
;; obligation #16
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$hyp "v'24" (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)
$hyp "v'25" (= a_CONSTANTunde_yunde_a
a_CONSTANTunde_yunde_a)
$hyp "v'26" (= a_CONSTANTunde_zunde_a
a_CONSTANTunde_zunde_a)
$hyp "v'27" (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)
$hyp "v'28" (= a_CONSTANTunde_kunde_a
a_CONSTANTunde_kunde_a)
$hyp "v'29" (= a_CONSTANTunde_lunde_a a_CONSTANTunde_lunde_a)
$hyp "v'30" (= 0 0)
$hyp "v'31" (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)
$hyp "v'32" (= a_CONSTANTunde_yunde_a
a_CONSTANTunde_yunde_a)
$hyp "v'33" (= a_CONSTANTunde_zunde_a
a_CONSTANTunde_zunde_a)
$hyp "v'34" (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)
$hyp "v'35" (= a_CONSTANTunde_kunde_a
a_CONSTANTunde_kunde_a)
$hyp "v'36" (= a_CONSTANTunde_lunde_a
a_CONSTANTunde_lunde_a)
$hyp "v'37" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$goal (/\ (/\ (/\ (/\ (/\ (/\ (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_yunde_a a_CONSTANTunde_yunde_a))
(= a_CONSTANTunde_zunde_a a_CONSTANTunde_zunde_a)) (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)) (= a_CONSTANTunde_kunde_a a_CONSTANTunde_kunde_a))
(= a_CONSTANTunde_lunde_a a_CONSTANTunde_lunde_a))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ho:"(~(((((((a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a)&(a_CONSTANTunde_yunde_a=a_CONSTANTunde_yunde_a))&(a_CONSTANTunde_zunde_a=a_CONSTANTunde_zunde_a))&(a_CONSTANTunde_junde_a=a_CONSTANTunde_junde_a))&(a_CONSTANTunde_kunde_a=a_CONSTANTunde_kunde_a))&(a_CONSTANTunde_lunde_a=a_CONSTANTunde_lunde_a))&(2=2)))" (is "~(?z_hq&?z_hbb)")
 show FALSE
 proof (rule zenon_notand [OF z_Ho])
  assume z_Hbd:"(~?z_hq)" (is "~(?z_hr&?z_hl)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbd])
   assume z_Hbe:"(~?z_hr)" (is "~(?z_hs&?z_hk)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbe])
    assume z_Hbf:"(~?z_hs)" (is "~(?z_ht&?z_hj)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbf])
     assume z_Hbg:"(~?z_ht)" (is "~(?z_hu&?z_hi)")
     show FALSE
     proof (rule zenon_notand [OF z_Hbg])
      assume z_Hbh:"(~?z_hu)" (is "~(?z_hg&?z_hh)")
      show FALSE
      proof (rule zenon_notand [OF z_Hbh])
       assume z_Hbi:"(a_CONSTANTunde_xunde_a~=a_CONSTANTunde_xunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbi])
      next
       assume z_Hbj:"(a_CONSTANTunde_yunde_a~=a_CONSTANTunde_yunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbj])
      qed
     next
      assume z_Hbk:"(a_CONSTANTunde_zunde_a~=a_CONSTANTunde_zunde_a)"
      show FALSE
      by (rule zenon_noteq [OF z_Hbk])
     qed
    next
     assume z_Hbl:"(a_CONSTANTunde_junde_a~=a_CONSTANTunde_junde_a)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbl])
    qed
   next
    assume z_Hbm:"(a_CONSTANTunde_kunde_a~=a_CONSTANTunde_kunde_a)"
    show FALSE
    by (rule zenon_noteq [OF z_Hbm])
   qed
  next
   assume z_Hbn:"(a_CONSTANTunde_lunde_a~=a_CONSTANTunde_lunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hbn])
  qed
 next
  assume z_Hbo:"(2~=2)" (is "?z_hbc~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbo])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 16"; *} qed
lemma ob'14:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
shows "(((((((((((((((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a))) \<and> (((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a))))) \<and> (((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a))))) \<and> (((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a))))) \<and> (((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a))))) \<and> (((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a))))) \<and> ((((0)) = ((0))))))"(is "PROP ?ob'14")
proof -
ML_command {* writeln "*** TLAPS ENTER 14"; *}
show "PROP ?ob'14"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_698c59.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_698c59.znn.out
;; obligation #14
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$goal (/\ (/\ (/\ (/\ (/\ (/\ (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_yunde_a a_CONSTANTunde_yunde_a))
(= a_CONSTANTunde_zunde_a a_CONSTANTunde_zunde_a)) (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)) (= a_CONSTANTunde_kunde_a a_CONSTANTunde_kunde_a))
(= a_CONSTANTunde_lunde_a a_CONSTANTunde_lunde_a)) (= 0
0))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hg:"(~(((((((a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a)&(a_CONSTANTunde_yunde_a=a_CONSTANTunde_yunde_a))&(a_CONSTANTunde_zunde_a=a_CONSTANTunde_zunde_a))&(a_CONSTANTunde_junde_a=a_CONSTANTunde_junde_a))&(a_CONSTANTunde_kunde_a=a_CONSTANTunde_kunde_a))&(a_CONSTANTunde_lunde_a=a_CONSTANTunde_lunde_a))&(0=0)))" (is "~(?z_hi&?z_hz)")
 show FALSE
 proof (rule zenon_notand [OF z_Hg])
  assume z_Hbb:"(~?z_hi)" (is "~(?z_hj&?z_hx)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbb])
   assume z_Hbc:"(~?z_hj)" (is "~(?z_hk&?z_hv)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbc])
    assume z_Hbd:"(~?z_hk)" (is "~(?z_hl&?z_ht)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbd])
     assume z_Hbe:"(~?z_hl)" (is "~(?z_hm&?z_hr)")
     show FALSE
     proof (rule zenon_notand [OF z_Hbe])
      assume z_Hbf:"(~?z_hm)" (is "~(?z_hn&?z_hp)")
      show FALSE
      proof (rule zenon_notand [OF z_Hbf])
       assume z_Hbg:"(a_CONSTANTunde_xunde_a~=a_CONSTANTunde_xunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbg])
      next
       assume z_Hbh:"(a_CONSTANTunde_yunde_a~=a_CONSTANTunde_yunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbh])
      qed
     next
      assume z_Hbi:"(a_CONSTANTunde_zunde_a~=a_CONSTANTunde_zunde_a)"
      show FALSE
      by (rule zenon_noteq [OF z_Hbi])
     qed
    next
     assume z_Hbj:"(a_CONSTANTunde_junde_a~=a_CONSTANTunde_junde_a)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbj])
    qed
   next
    assume z_Hbk:"(a_CONSTANTunde_kunde_a~=a_CONSTANTunde_kunde_a)"
    show FALSE
    by (rule zenon_noteq [OF z_Hbk])
   qed
  next
   assume z_Hbl:"(a_CONSTANTunde_lunde_a~=a_CONSTANTunde_lunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hbl])
  qed
 next
  assume z_Hbm:"(0~=0)"
  show FALSE
  by (rule zenon_noteq [OF z_Hbm])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 14"; *} qed
lemma ob'17:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
assumes v'24: "(((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))"
assumes v'25: "(((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a)))"
assumes v'26: "(((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a)))"
assumes v'27: "(((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a)))"
assumes v'28: "(((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a)))"
assumes v'29: "(((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a)))"
assumes v'30: "((((0)) = ((0))))"
assumes v'31: "(((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))"
assumes v'32: "(((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a)))"
assumes v'33: "(((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a)))"
assumes v'34: "(((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a)))"
assumes v'35: "(((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a)))"
assumes v'36: "(((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a)))"
assumes v'37: "((((Succ[0])) = ((Succ[0]))))"
assumes v'38: "(((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))"
assumes v'39: "(((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a)))"
assumes v'40: "(((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a)))"
assumes v'41: "(((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a)))"
assumes v'42: "(((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a)))"
assumes v'43: "(((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a)))"
assumes v'44: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
shows "(((((((((((((((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a))) \<and> (((a_CONSTANTunde_yunde_a) = (a_CONSTANTunde_yunde_a))))) \<and> (((a_CONSTANTunde_zunde_a) = (a_CONSTANTunde_zunde_a))))) \<and> (((a_CONSTANTunde_junde_a) = (a_CONSTANTunde_junde_a))))) \<and> (((a_CONSTANTunde_kunde_a) = (a_CONSTANTunde_kunde_a))))) \<and> (((a_CONSTANTunde_lunde_a) = (a_CONSTANTunde_lunde_a))))) \<and> ((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))))"(is "PROP ?ob'17")
proof -
ML_command {* writeln "*** TLAPS ENTER 17"; *}
show "PROP ?ob'17"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_d22ff7.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_d22ff7.znn.out
;; obligation #17
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$hyp "v'24" (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)
$hyp "v'25" (= a_CONSTANTunde_yunde_a
a_CONSTANTunde_yunde_a)
$hyp "v'26" (= a_CONSTANTunde_zunde_a
a_CONSTANTunde_zunde_a)
$hyp "v'27" (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)
$hyp "v'28" (= a_CONSTANTunde_kunde_a
a_CONSTANTunde_kunde_a)
$hyp "v'29" (= a_CONSTANTunde_lunde_a a_CONSTANTunde_lunde_a)
$hyp "v'30" (= 0 0)
$hyp "v'31" (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)
$hyp "v'32" (= a_CONSTANTunde_yunde_a
a_CONSTANTunde_yunde_a)
$hyp "v'33" (= a_CONSTANTunde_zunde_a
a_CONSTANTunde_zunde_a)
$hyp "v'34" (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)
$hyp "v'35" (= a_CONSTANTunde_kunde_a
a_CONSTANTunde_kunde_a)
$hyp "v'36" (= a_CONSTANTunde_lunde_a
a_CONSTANTunde_lunde_a)
$hyp "v'37" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'38" (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)
$hyp "v'39" (= a_CONSTANTunde_yunde_a
a_CONSTANTunde_yunde_a)
$hyp "v'40" (= a_CONSTANTunde_zunde_a
a_CONSTANTunde_zunde_a)
$hyp "v'41" (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)
$hyp "v'42" (= a_CONSTANTunde_kunde_a
a_CONSTANTunde_kunde_a)
$hyp "v'43" (= a_CONSTANTunde_lunde_a
a_CONSTANTunde_lunde_a)
$hyp "v'44" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$goal (/\ (/\ (/\ (/\ (/\ (/\ (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_yunde_a a_CONSTANTunde_yunde_a))
(= a_CONSTANTunde_zunde_a a_CONSTANTunde_zunde_a)) (= a_CONSTANTunde_junde_a
a_CONSTANTunde_junde_a)) (= a_CONSTANTunde_kunde_a a_CONSTANTunde_kunde_a))
(= a_CONSTANTunde_lunde_a a_CONSTANTunde_lunde_a))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hp:"(~(((((((a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a)&(a_CONSTANTunde_yunde_a=a_CONSTANTunde_yunde_a))&(a_CONSTANTunde_zunde_a=a_CONSTANTunde_zunde_a))&(a_CONSTANTunde_junde_a=a_CONSTANTunde_junde_a))&(a_CONSTANTunde_kunde_a=a_CONSTANTunde_kunde_a))&(a_CONSTANTunde_lunde_a=a_CONSTANTunde_lunde_a))&(3=3)))" (is "~(?z_hr&?z_hbc)")
 show FALSE
 proof (rule zenon_notand [OF z_Hp])
  assume z_Hbe:"(~?z_hr)" (is "~(?z_hs&?z_hl)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbe])
   assume z_Hbf:"(~?z_hs)" (is "~(?z_ht&?z_hk)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbf])
    assume z_Hbg:"(~?z_ht)" (is "~(?z_hu&?z_hj)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbg])
     assume z_Hbh:"(~?z_hu)" (is "~(?z_hv&?z_hi)")
     show FALSE
     proof (rule zenon_notand [OF z_Hbh])
      assume z_Hbi:"(~?z_hv)" (is "~(?z_hg&?z_hh)")
      show FALSE
      proof (rule zenon_notand [OF z_Hbi])
       assume z_Hbj:"(a_CONSTANTunde_xunde_a~=a_CONSTANTunde_xunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbj])
      next
       assume z_Hbk:"(a_CONSTANTunde_yunde_a~=a_CONSTANTunde_yunde_a)"
       show FALSE
       by (rule zenon_noteq [OF z_Hbk])
      qed
     next
      assume z_Hbl:"(a_CONSTANTunde_zunde_a~=a_CONSTANTunde_zunde_a)"
      show FALSE
      by (rule zenon_noteq [OF z_Hbl])
     qed
    next
     assume z_Hbm:"(a_CONSTANTunde_junde_a~=a_CONSTANTunde_junde_a)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbm])
    qed
   next
    assume z_Hbn:"(a_CONSTANTunde_kunde_a~=a_CONSTANTunde_kunde_a)"
    show FALSE
    by (rule zenon_noteq [OF z_Hbn])
   qed
  next
   assume z_Hbo:"(a_CONSTANTunde_lunde_a~=a_CONSTANTunde_lunde_a)"
   show FALSE
   by (rule zenon_noteq [OF z_Hbo])
  qed
 next
  assume z_Hbp:"(3~=3)" (is "?z_hbd~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hbp])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 17"; *} qed
lemma ob'19:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
assumes v'22: "(''set enums, tuples, records, record sets'')"
assumes v'25: "((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))))))))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
shows "((((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))))) \<and> ((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))))"(is "PROP ?ob'19")
proof -
ML_command {* writeln "*** TLAPS ENTER 19"; *}
show "PROP ?ob'19"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_26c97e.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_26c97e.znn.out
;; obligation #19
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$hyp "v'22" "set enums, tuples, records, record sets"
$hyp "v'25" (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)))
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$goal (/\ (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a)))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hj:"(~((a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a))=a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a)))&(2=2)))" (is "~(?z_hh&?z_hr)")
 show FALSE
 proof (rule zenon_notand [OF z_Hj])
  assume z_Ht:"(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a))~=a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a)))" (is "?z_hl~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Ht])
 next
  assume z_Hu:"(2~=2)" (is "?z_hs~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hu])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 19"; *} qed
lemma ob'18:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
assumes v'22: "(''set enums, tuples, records, record sets'')"
shows "((((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))))) \<and> ((((Succ[0])) = ((Succ[0]))))))"(is "PROP ?ob'18")
proof -
ML_command {* writeln "*** TLAPS ENTER 18"; *}
show "PROP ?ob'18"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_631e47.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_631e47.znn.out
;; obligation #18
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$hyp "v'22" "set enums, tuples, records, record sets"
$goal (/\ (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a)))
(= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hh:"(~((a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a))=a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a)))&(1=1)))" (is "~(?z_hj&?z_hq)")
 show FALSE
 proof (rule zenon_notand [OF z_Hh])
  assume z_Hs:"(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a))~=a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10), a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a)))" (is "?z_hk~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hs])
 next
  assume z_Ht:"(1~=1)" (is "?z_hr~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Ht])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 18"; *} qed
lemma ob'20:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
assumes v'22: "(''set enums, tuples, records, record sets'')"
assumes v'25: "((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))))))))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))))))))"
assumes v'28: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
shows "((((((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))) = ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))))) \<and> ((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))))"(is "PROP ?ob'20")
proof -
ML_command {* writeln "*** TLAPS ENTER 20"; *}
show "PROP ?ob'20"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_7940ec.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_7940ec.znn.out
;; obligation #20
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$hyp "v'22" "set enums, tuples, records, record sets"
$hyp "v'25" (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)))
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)))
$hyp "v'28" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$goal (/\ (= (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)) (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hk:"(~((a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a)=a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a))&(2=2)))" (is "~(?z_hm&?z_hj)")
 show FALSE
 proof (rule zenon_notand [OF z_Hk])
  assume z_Hr:"(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a)~=a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a))" (is "?z_hn~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hr])
 next
  assume z_Hs:"(2~=2)" (is "?z_hq~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hs])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 20"; *} qed
lemma ob'21:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'19: "(''ordinary TLA+ operators'')"
assumes v'20: "(''if/then/else'')"
assumes v'21: "(''expressions that introduce binders'')"
assumes v'22: "(''set enums, tuples, records, record sets'')"
assumes v'25: "((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))))))))"
assumes v'26: "((((Succ[0])) = ((Succ[0]))))"
assumes v'27: "((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))))))))"
assumes v'28: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
assumes v'29: "((((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))) = ((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a))))))"
assumes v'30: "((((Succ[Succ[0]])) = ((Succ[Succ[0]]))))"
shows "((((((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))) = ((a_CONSTANTunde_plus_unde_a (((a_CONSTANTunde_plus_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))))) \<and> ((((Succ[Succ[Succ[0]]])) = ((Succ[Succ[Succ[0]]]))))))"(is "PROP ?ob'21")
proof -
ML_command {* writeln "*** TLAPS ENTER 21"; *}
show "PROP ?ob'21"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_56979c.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_56979c.znn.out
;; obligation #21
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'19" "ordinary TLA+ operators"
$hyp "v'20" "if/then/else"
$hyp "v'21" "expressions that introduce binders"
$hyp "v'22" "set enums, tuples, records, record sets"
$hyp "v'25" (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)))
$hyp "v'26" (= (TLA.fapply TLA.Succ 0)
(TLA.fapply TLA.Succ 0))
$hyp "v'27" (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a a_CONSTANTunde_yunde_a))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)))
$hyp "v'28" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$hyp "v'29" (= (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a))
$hyp "v'30" (= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
$goal (/\ (= (a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_plus_unde_a (a_CONSTANTunde_plus_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a)
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
(= (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hl:"(~((a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10)=a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10))&(3=3)))" (is "~(?z_hn&?z_ht)")
 show FALSE
 proof (rule zenon_notand [OF z_Hl])
  assume z_Hv:"(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10)~=a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_plus_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), 10))" (is "?z_ho~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hv])
 next
  assume z_Hw:"(3~=3)" (is "?z_hu~=_")
  show FALSE
  by (rule zenon_noteq [OF z_Hw])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 21"; *} qed
lemma ob'22:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'17: "(''simple positional references'')"
assumes v'18: "(''positional selectors for ASSUME/PROVE'')"
shows "((((a_CONSTANTunde_Qunde_a (((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a))))))) = ((a_CONSTANTunde_Qunde_a (((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))))))"(is "PROP ?ob'22")
proof -
ML_command {* writeln "*** TLAPS ENTER 22"; *}
show "PROP ?ob'22"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_27202e.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_27202e.znn.out
;; obligation #22
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'17" "simple positional references"
$hyp "v'18" "positional selectors for ASSUME/PROVE"
$goal (= (a_CONSTANTunde_Qunde_a (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a))
(a_CONSTANTunde_Qunde_a (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hf:"(a_CONSTANTunde_Qunde_a(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_zunde_a, a_CONSTANTunde_junde_a))~=a_CONSTANTunde_Qunde_a(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_zunde_a, a_CONSTANTunde_junde_a)))" (is "?z_hg~=_")
 show FALSE
 by (rule zenon_noteq [OF z_Hf])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 22"; *} qed
lemma ob'24:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'17: "(''simple positional references'')"
assumes v'18: "(''positional selectors for ASSUME/PROVE'')"
assumes v'21: "(''example from page 9 of tla2.pdf of October 14, 2009'')"
shows "((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]])), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]]]]]]]]]]]))))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]])), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]]]]]]]]]]]))))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]])))))))"(is "PROP ?ob'24")
proof -
ML_command {* writeln "*** TLAPS ENTER 24"; *}
show "PROP ?ob'24"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_8ef7ed.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_8ef7ed.znn.out
;; obligation #24
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'17" "simple positional references"
$hyp "v'18" "positional selectors for ASSUME/PROVE"
$hyp "v'21" "example from page 9 of tla2.pdf of October 14, 2009"
$goal (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hg:"(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(10, (Succ[(Succ[(Succ[(Succ[(Succ[15])])])])])), 10)~=a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a(10, (Succ[(Succ[(Succ[(Succ[(Succ[15])])])])])), 10))" (is "?z_hh~=_")
 show FALSE
 by (rule zenon_noteq [OF z_Hg])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 24"; *} qed
lemma ob'23:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'17: "(''simple positional references'')"
assumes v'18: "(''positional selectors for ASSUME/PROVE'')"
assumes v'23: "((((a_CONSTANTunde_Qunde_a (((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a))))))) = ((a_CONSTANTunde_Qunde_a (((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_zunde_a), (a_CONSTANTunde_junde_a)))))))))"
shows "((((a_CONSTANTunde_Qunde_a (((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_zunde_a))))))) = ((a_CONSTANTunde_Qunde_a (((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_xunde_a), (a_CONSTANTunde_yunde_a)))), ((a_CONSTANTunde_dash_unde_a ((a_CONSTANTunde_junde_a), (a_CONSTANTunde_zunde_a)))))))))"(is "PROP ?ob'23")
proof -
ML_command {* writeln "*** TLAPS ENTER 23"; *}
show "PROP ?ob'23"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_e50e1c.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_e50e1c.znn.out
;; obligation #23
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'17" "simple positional references"
$hyp "v'18" "positional selectors for ASSUME/PROVE"
$hyp "v'23" (= (a_CONSTANTunde_Qunde_a (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a))
(a_CONSTANTunde_Qunde_a (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_zunde_a
a_CONSTANTunde_junde_a)))
$goal (= (a_CONSTANTunde_Qunde_a (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_junde_a
a_CONSTANTunde_zunde_a))
(a_CONSTANTunde_Qunde_a (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a) (a_CONSTANTunde_dash_unde_a a_CONSTANTunde_junde_a
a_CONSTANTunde_zunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hg:"(a_CONSTANTunde_Qunde_a(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_junde_a, a_CONSTANTunde_zunde_a))~=a_CONSTANTunde_Qunde_a(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_xunde_a, a_CONSTANTunde_yunde_a), a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_junde_a, a_CONSTANTunde_zunde_a)))" (is "?z_hh~=_")
 show FALSE
 by (rule zenon_noteq [OF z_Hg])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 23"; *} qed
lemma ob'25:
fixes a_CONSTANTunde_plus_unde_a
fixes a_CONSTANTunde_dash_unde_a
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_Cunde_a
fixes a_CONSTANTunde_Punde_a
fixes a_CONSTANTunde_Qunde_a
fixes a_CONSTANTunde_Runde_a
fixes a_CONSTANTunde_Sunde_a
fixes a_CONSTANTunde_Tunde_a
fixes a_CONSTANTunde_Uunde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_zunde_a
assumes a_CONSTANTunde_zunde_a_in : "(a_CONSTANTunde_zunde_a \<in> (a_CONSTANTunde_Sunde_a))"
fixes a_CONSTANTunde_junde_a
fixes a_CONSTANTunde_kunde_a
fixes a_CONSTANTunde_lunde_a
assumes v'17: "(''simple positional references'')"
assumes v'18: "(''positional selectors for ASSUME/PROVE'')"
assumes v'21: "(''example from page 9 of tla2.pdf of October 14, 2009'')"
assumes v'24: "(''labelled subexpr. in scope of definitions'')"
shows "((((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]]]]]]]]]]])), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))) = ((a_CONSTANTunde_dash_unde_a (((a_CONSTANTunde_plus_unde_a (((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]]]]]]]]]]])), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]]))))), ((Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[Succ[0]]]]]]]]]])))))))"(is "PROP ?ob'25")
proof -
ML_command {* writeln "*** TLAPS ENTER 25"; *}
show "PROP ?ob'25"

(* BEGIN ZENON INPUT
;; file=.tlacache/Subref_test.tlaps/tlapm_452dab.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Subref_test.tlaps/tlapm_452dab.znn.out
;; obligation #25
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a a_CONSTANTunde_Sunde_a)
$hyp "a_CONSTANTunde_zunde_a_in" (TLA.in a_CONSTANTunde_zunde_a a_CONSTANTunde_Sunde_a)
$hyp "v'17" "simple positional references"
$hyp "v'18" "positional selectors for ASSUME/PROVE"
$hyp "v'21" "example from page 9 of tla2.pdf of October 14, 2009"
$hyp "v'24" "labelled subexpr. in scope of definitions"
$goal (= (a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(a_CONSTANTunde_dash_unde_a (a_CONSTANTunde_plus_unde_a (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))))))))))
(TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hh:"(a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a((Succ[(Succ[(Succ[(Succ[(Succ[15])])])])]), 10), 10)~=a_CONSTANTunde_dash_unde_a(a_CONSTANTunde_plus_unde_a((Succ[(Succ[(Succ[(Succ[(Succ[15])])])])]), 10), 10))" (is "?z_hi~=_")
 show FALSE
 by (rule zenon_noteq [OF z_Hh])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 25"; *} qed
end

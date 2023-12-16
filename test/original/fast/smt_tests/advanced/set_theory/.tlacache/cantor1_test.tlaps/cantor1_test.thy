(* automatically generated -- do not edit manually *)
theory cantor1_test imports Constant Zenon begin
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
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
(* usable definition CONSTANT_Surjective_ suppressed *)
fixes a_CONSTANTunde_Eunde_a
fixes a_CONSTANTunde_funde_a
assumes a_CONSTANTunde_funde_a_in : "(a_CONSTANTunde_funde_a \<in> ([(a_CONSTANTunde_Eunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Eunde_a)))]))"
assumes v'10: "(((subsetOf((a_CONSTANTunde_Eunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))))))) \<in> ((SUBSET (a_CONSTANTunde_Eunde_a)))))"
assumes v'13: "(\<forall> a_CONSTANTunde_Punde_a \<in> ((SUBSET (a_CONSTANTunde_Eunde_a))) : (\<exists> a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Eunde_a) : (((fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))) = (a_CONSTANTunde_Punde_a)))))"
shows "(\<exists> a_CONSTANTunde_dunde_a \<in> (a_CONSTANTunde_Eunde_a) : (((fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_dunde_a))) = (subsetOf((a_CONSTANTunde_Eunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))))))))))"(is "PROP ?ob'6")
proof -
ML_command {* writeln "*** TLAPS ENTER 6"; *}
show "PROP ?ob'6"

(* BEGIN ZENON INPUT
;; file=.tlacache/cantor1_test.tlaps/tlapm_6e1a01.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/cantor1_test.tlaps/tlapm_6e1a01.znn.out
;; obligation #6
$hyp "a_CONSTANTunde_funde_a_in" (TLA.in a_CONSTANTunde_funde_a (TLA.FuncSet a_CONSTANTunde_Eunde_a (TLA.SUBSET a_CONSTANTunde_Eunde_a)))
$hyp "v'10" (TLA.in (TLA.subsetOf a_CONSTANTunde_Eunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
(TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a)))))
(TLA.SUBSET a_CONSTANTunde_Eunde_a))
$hyp "v'13" (TLA.bAll (TLA.SUBSET a_CONSTANTunde_Eunde_a) ((a_CONSTANTunde_Punde_a) (TLA.bEx a_CONSTANTunde_Eunde_a ((a_CONSTANTunde_xunde_a) (= (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a)
a_CONSTANTunde_Punde_a)))))
$goal (TLA.bEx a_CONSTANTunde_Eunde_a ((a_CONSTANTunde_dunde_a) (= (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_dunde_a)
(TLA.subsetOf a_CONSTANTunde_Eunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
(TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hc:"bAll(SUBSET(a_CONSTANTunde_Eunde_a), (\<lambda>a_CONSTANTunde_Punde_a. bEx(a_CONSTANTunde_Eunde_a, (\<lambda>a_CONSTANTunde_xunde_a. ((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])=a_CONSTANTunde_Punde_a)))))" (is "?z_hc")
 using v'13 by blast
 have z_Hb:"(subsetOf(a_CONSTANTunde_Eunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in (a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]))))) \\in SUBSET(a_CONSTANTunde_Eunde_a))" (is "?z_hb")
 using v'10 by blast
 assume z_Hd:"(~bEx(a_CONSTANTunde_Eunde_a, (\<lambda>a_CONSTANTunde_dunde_a. ((a_CONSTANTunde_funde_a[a_CONSTANTunde_dunde_a])=subsetOf(a_CONSTANTunde_Eunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in (a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])))))))))" (is "~?z_hs")
 have z_Hx_z_Hc: "(\\A x:((x \\in SUBSET(a_CONSTANTunde_Eunde_a))=>bEx(a_CONSTANTunde_Eunde_a, (\<lambda>a_CONSTANTunde_xunde_a. ((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])=x))))) == ?z_hc" (is "?z_hx == _")
 by (unfold bAll_def)
 have z_Hx: "?z_hx" (is "\\A x : ?z_hbe(x)")
 by (unfold z_Hx_z_Hc, fact z_Hc)
 have z_Hbf: "?z_hbe(subsetOf(a_CONSTANTunde_Eunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in (a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]))))))"
 by (rule zenon_all_0 [of "?z_hbe" "subsetOf(a_CONSTANTunde_Eunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in (a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])))))", OF z_Hx])
 show FALSE
 proof (rule zenon_imply [OF z_Hbf])
  assume z_Hbg:"(~?z_hb)"
  show FALSE
  by (rule notE [OF z_Hbg z_Hb])
 next
  assume z_Hs:"?z_hs"
  show FALSE
  by (rule notE [OF z_Hd z_Hs])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 6"; *} qed
end

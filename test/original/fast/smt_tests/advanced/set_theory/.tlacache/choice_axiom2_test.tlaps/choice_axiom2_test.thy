(* automatically generated -- do not edit manually *)
theory choice_axiom2_test imports Constant Zenon begin
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

lemma ob'4:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Iunde_a
fixes a_CONSTANTunde_Xunde_a
fixes a_CONSTANTunde_aunde_a
assumes a_CONSTANTunde_aunde_a_in : "(a_CONSTANTunde_aunde_a \<in> ([(a_CONSTANTunde_Iunde_a) \<rightarrow> (a_CONSTANTunde_Xunde_a)]))"
assumes v'13: "(\<forall> a_CONSTANTunde_iunde_a \<in> (a_CONSTANTunde_Iunde_a) : (((fapply ((([ a_CONSTANTunde_iunde_a_1 \<in> (a_CONSTANTunde_Iunde_a)  \<mapsto> (bChoice((fapply ((a_CONSTANTunde_aunde_a), (a_CONSTANTunde_iunde_a_1))), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))))])), (a_CONSTANTunde_iunde_a))) \<in> (fapply ((a_CONSTANTunde_aunde_a), (a_CONSTANTunde_iunde_a))))))"
assumes v'14: "((([ a_CONSTANTunde_iunde_a \<in> (a_CONSTANTunde_Iunde_a)  \<mapsto> (bChoice((fapply ((a_CONSTANTunde_aunde_a), (a_CONSTANTunde_iunde_a))), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) = (a_CONSTANTunde_xunde_a)))))]) \<in> ([(a_CONSTANTunde_Iunde_a) \<rightarrow> ((UNION (setOfAll((a_CONSTANTunde_Iunde_a), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_aunde_a), (a_CONSTANTunde_iunde_a)))))))])))"
shows "(\<exists> a_CONSTANTunde_funde_a \<in> ([(a_CONSTANTunde_Iunde_a) \<rightarrow> ((UNION (setOfAll((a_CONSTANTunde_Iunde_a), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_aunde_a), (a_CONSTANTunde_iunde_a)))))))]) : (\<forall> a_CONSTANTunde_iunde_a \<in> (a_CONSTANTunde_Iunde_a) : (((fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_iunde_a))) \<in> (fapply ((a_CONSTANTunde_aunde_a), (a_CONSTANTunde_iunde_a)))))))"(is "PROP ?ob'4")
proof -
ML_command {* writeln "*** TLAPS ENTER 4"; *}
show "PROP ?ob'4"

(* BEGIN ZENON INPUT
;; file=.tlacache/choice_axiom2_test.tlaps/tlapm_2ab342.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/choice_axiom2_test.tlaps/tlapm_2ab342.znn.out
;; obligation #4
$hyp "a_CONSTANTunde_aunde_a_in" (TLA.in a_CONSTANTunde_aunde_a (TLA.FuncSet a_CONSTANTunde_Iunde_a a_CONSTANTunde_Xunde_a))
$hyp "v'13" (TLA.bAll a_CONSTANTunde_Iunde_a ((a_CONSTANTunde_iunde_a) (TLA.in (TLA.fapply (TLA.Fcn a_CONSTANTunde_Iunde_a ((a_CONSTANTunde_iunde_a_1) (TLA.bChoice (TLA.fapply a_CONSTANTunde_aunde_a a_CONSTANTunde_iunde_a_1) ((a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a))))) a_CONSTANTunde_iunde_a)
(TLA.fapply a_CONSTANTunde_aunde_a a_CONSTANTunde_iunde_a))))
$hyp "v'14" (TLA.in (TLA.Fcn a_CONSTANTunde_Iunde_a ((a_CONSTANTunde_iunde_a) (TLA.bChoice (TLA.fapply a_CONSTANTunde_aunde_a a_CONSTANTunde_iunde_a) ((a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)))))
(TLA.FuncSet a_CONSTANTunde_Iunde_a (TLA.UNION (TLA.setOfAll a_CONSTANTunde_Iunde_a ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_aunde_a a_CONSTANTunde_iunde_a))))))
$goal (TLA.bEx (TLA.FuncSet a_CONSTANTunde_Iunde_a (TLA.UNION (TLA.setOfAll a_CONSTANTunde_Iunde_a ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_aunde_a a_CONSTANTunde_iunde_a))))) ((a_CONSTANTunde_funde_a) (TLA.bAll a_CONSTANTunde_Iunde_a ((a_CONSTANTunde_iunde_a) (TLA.in (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_iunde_a)
(TLA.fapply a_CONSTANTunde_aunde_a a_CONSTANTunde_iunde_a))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"bAll(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a. ((Fcn(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a_1. bChoice((a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a_1]), (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a)))))[a_CONSTANTunde_iunde_a]) \\in (a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a]))))" (is "?z_hb")
 using v'13 by blast
 have z_Hc:"(Fcn(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a_1. bChoice((a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a_1]), (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a))))) \\in FuncSet(a_CONSTANTunde_Iunde_a, UNION(setOfAll(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a]))))))" (is "?z_hc")
 using v'14 by blast
 assume z_Hd:"(~bEx(FuncSet(a_CONSTANTunde_Iunde_a, UNION(setOfAll(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a]))))), (\<lambda>a_CONSTANTunde_funde_a. bAll(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a. ((a_CONSTANTunde_funde_a[a_CONSTANTunde_iunde_a]) \\in (a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a])))))))" (is "~?z_hx")
 have z_Hbe_z_Hd: "(~(\\E x:((x \\in FuncSet(a_CONSTANTunde_Iunde_a, UNION(setOfAll(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a]))))))&bAll(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a. ((x[a_CONSTANTunde_iunde_a]) \\in (a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a]))))))) == (~?z_hx)" (is "?z_hbe == ?z_hd")
 by (unfold bEx_def)
 have z_Hbe: "?z_hbe" (is "~(\\E x : ?z_hbn(x))")
 by (unfold z_Hbe_z_Hd, fact z_Hd)
 have z_Hbo: "~?z_hbn(Fcn(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a_1. bChoice((a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a_1]), (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a))))))"
 by (rule zenon_notex_0 [of "?z_hbn" "Fcn(a_CONSTANTunde_Iunde_a, (\<lambda>a_CONSTANTunde_iunde_a_1. bChoice((a_CONSTANTunde_aunde_a[a_CONSTANTunde_iunde_a_1]), (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a)))))", OF z_Hbe])
 show FALSE
 proof (rule zenon_notand [OF z_Hbo])
  assume z_Hbp:"(~?z_hc)"
  show FALSE
  by (rule notE [OF z_Hbp z_Hc])
 next
  assume z_Hbq:"(~?z_hb)"
  show FALSE
  by (rule notE [OF z_Hbq z_Hb])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 4"; *} qed
end

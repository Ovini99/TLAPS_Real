(* automatically generated -- do not edit manually *)
theory section_test imports Constant Zenon begin
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
(* usable definition CONSTANT_Surjective_ suppressed *)
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_funde_a
assumes a_CONSTANTunde_funde_a_in : "(a_CONSTANTunde_funde_a \<in> ([(a_CONSTANTunde_Aunde_a) \<rightarrow> (a_CONSTANTunde_Bunde_a)]))"
assumes v'13: "(\<forall> a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Bunde_a) : (((fapply ((a_CONSTANTunde_funde_a), (fapply ((([ a_CONSTANTunde_yunde_a_1 \<in> (a_CONSTANTunde_Bunde_a)  \<mapsto> (bChoice((a_CONSTANTunde_Aunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_yunde_a_1) = (fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a)))))))])), (a_CONSTANTunde_yunde_a))))) = (a_CONSTANTunde_yunde_a))))"
assumes v'14: "((([ a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Bunde_a)  \<mapsto> (bChoice((a_CONSTANTunde_Aunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_yunde_a) = (fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a)))))))]) \<in> ([(a_CONSTANTunde_Bunde_a) \<rightarrow> (a_CONSTANTunde_Aunde_a)])))"
shows "(\<exists> a_CONSTANTunde_gunde_a \<in> ([(a_CONSTANTunde_Bunde_a) \<rightarrow> (a_CONSTANTunde_Aunde_a)]) : (\<forall> a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Bunde_a) : (((fapply ((a_CONSTANTunde_funde_a), (fapply ((a_CONSTANTunde_gunde_a), (a_CONSTANTunde_yunde_a))))) = (a_CONSTANTunde_yunde_a)))))"(is "PROP ?ob'4")
proof -
ML_command {* writeln "*** TLAPS ENTER 4"; *}
show "PROP ?ob'4"

(* BEGIN ZENON INPUT
;; file=.tlacache/section_test.tlaps/tlapm_8214a2.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/section_test.tlaps/tlapm_8214a2.znn.out
;; obligation #4
$hyp "a_CONSTANTunde_funde_a_in" (TLA.in a_CONSTANTunde_funde_a (TLA.FuncSet a_CONSTANTunde_Aunde_a a_CONSTANTunde_Bunde_a))
$hyp "v'13" (TLA.bAll a_CONSTANTunde_Bunde_a ((a_CONSTANTunde_yunde_a) (= (TLA.fapply a_CONSTANTunde_funde_a (TLA.fapply (TLA.Fcn a_CONSTANTunde_Bunde_a ((a_CONSTANTunde_yunde_a_1) (TLA.bChoice a_CONSTANTunde_Aunde_a ((a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_yunde_a_1
(TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a)))))) a_CONSTANTunde_yunde_a))
a_CONSTANTunde_yunde_a)))
$hyp "v'14" (TLA.in (TLA.Fcn a_CONSTANTunde_Bunde_a ((a_CONSTANTunde_yunde_a) (TLA.bChoice a_CONSTANTunde_Aunde_a ((a_CONSTANTunde_xunde_a) (= a_CONSTANTunde_yunde_a
(TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a))))))
(TLA.FuncSet a_CONSTANTunde_Bunde_a a_CONSTANTunde_Aunde_a))
$goal (TLA.bEx (TLA.FuncSet a_CONSTANTunde_Bunde_a a_CONSTANTunde_Aunde_a) ((a_CONSTANTunde_gunde_a) (TLA.bAll a_CONSTANTunde_Bunde_a ((a_CONSTANTunde_yunde_a) (= (TLA.fapply a_CONSTANTunde_funde_a (TLA.fapply a_CONSTANTunde_gunde_a a_CONSTANTunde_yunde_a))
a_CONSTANTunde_yunde_a)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"bAll(a_CONSTANTunde_Bunde_a, (\<lambda>a_CONSTANTunde_yunde_a. ((a_CONSTANTunde_funde_a[(Fcn(a_CONSTANTunde_Bunde_a, (\<lambda>a_CONSTANTunde_yunde_a_1. bChoice(a_CONSTANTunde_Aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_yunde_a_1=(a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]))))))[a_CONSTANTunde_yunde_a])])=a_CONSTANTunde_yunde_a)))" (is "?z_hb")
 using v'13 by blast
 have z_Hc:"(Fcn(a_CONSTANTunde_Bunde_a, (\<lambda>a_CONSTANTunde_yunde_a_1. bChoice(a_CONSTANTunde_Aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_yunde_a_1=(a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])))))) \\in FuncSet(a_CONSTANTunde_Bunde_a, a_CONSTANTunde_Aunde_a))" (is "?z_hc")
 using v'14 by blast
 assume z_Hd:"(~bEx(FuncSet(a_CONSTANTunde_Bunde_a, a_CONSTANTunde_Aunde_a), (\<lambda>a_CONSTANTunde_gunde_a. bAll(a_CONSTANTunde_Bunde_a, (\<lambda>a_CONSTANTunde_yunde_a. ((a_CONSTANTunde_funde_a[(a_CONSTANTunde_gunde_a[a_CONSTANTunde_yunde_a])])=a_CONSTANTunde_yunde_a))))))" (is "~?z_hv")
 have z_Hbd_z_Hd: "(~(\\E x:((x \\in FuncSet(a_CONSTANTunde_Bunde_a, a_CONSTANTunde_Aunde_a))&bAll(a_CONSTANTunde_Bunde_a, (\<lambda>a_CONSTANTunde_yunde_a. ((a_CONSTANTunde_funde_a[(x[a_CONSTANTunde_yunde_a])])=a_CONSTANTunde_yunde_a)))))) == (~?z_hv)" (is "?z_hbd == ?z_hd")
 by (unfold bEx_def)
 have z_Hbd: "?z_hbd" (is "~(\\E x : ?z_hbn(x))")
 by (unfold z_Hbd_z_Hd, fact z_Hd)
 have z_Hbo: "~?z_hbn(Fcn(a_CONSTANTunde_Bunde_a, (\<lambda>a_CONSTANTunde_yunde_a_1. bChoice(a_CONSTANTunde_Aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_yunde_a_1=(a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])))))))"
 by (rule zenon_notex_0 [of "?z_hbn" "Fcn(a_CONSTANTunde_Bunde_a, (\<lambda>a_CONSTANTunde_yunde_a_1. bChoice(a_CONSTANTunde_Aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_yunde_a_1=(a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]))))))", OF z_Hbd])
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

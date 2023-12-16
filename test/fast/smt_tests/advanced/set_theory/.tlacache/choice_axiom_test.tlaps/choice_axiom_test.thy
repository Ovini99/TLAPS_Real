(* automatically generated -- do not edit manually *)
theory choice_axiom_test imports Constant Zenon begin
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

lemma ob'10:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_aunde_a
assumes v'14: "(\<forall> a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_aunde_a) : (((fapply ((([ a_CONSTANTunde_xunde_a_1 \<in> (a_CONSTANTunde_aunde_a)  \<mapsto> (Choice(%a_CONSTANTunde_yunde_a. (((a_CONSTANTunde_yunde_a) \<in> (a_CONSTANTunde_xunde_a_1)))))])), (a_CONSTANTunde_xunde_a))) \<in> (a_CONSTANTunde_xunde_a))))"
assumes v'15: "((([ a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_aunde_a)  \<mapsto> (Choice(%a_CONSTANTunde_yunde_a. (((a_CONSTANTunde_yunde_a) \<in> (a_CONSTANTunde_xunde_a)))))]) \<in> ([(a_CONSTANTunde_aunde_a) \<rightarrow> ((UNION (a_CONSTANTunde_aunde_a)))])))"
shows "(\<exists> a_CONSTANTunde_funde_a \<in> ([(a_CONSTANTunde_aunde_a) \<rightarrow> ((UNION (a_CONSTANTunde_aunde_a)))]) : (\<forall> a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_aunde_a) : (((fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))) \<in> (a_CONSTANTunde_xunde_a)))))"(is "PROP ?ob'10")
proof -
ML_command {* writeln "*** TLAPS ENTER 10"; *}
show "PROP ?ob'10"

(* BEGIN ZENON INPUT
;; file=.tlacache/choice_axiom_test.tlaps/tlapm_5719d9.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/choice_axiom_test.tlaps/tlapm_5719d9.znn.out
;; obligation #10
$hyp "v'14" (TLA.bAll a_CONSTANTunde_aunde_a ((a_CONSTANTunde_xunde_a) (TLA.in (TLA.fapply (TLA.Fcn a_CONSTANTunde_aunde_a ((a_CONSTANTunde_xunde_a_1) (t. ((a_CONSTANTunde_yunde_a) (TLA.in a_CONSTANTunde_yunde_a
a_CONSTANTunde_xunde_a_1))))) a_CONSTANTunde_xunde_a)
a_CONSTANTunde_xunde_a)))
$hyp "v'15" (TLA.in (TLA.Fcn a_CONSTANTunde_aunde_a ((a_CONSTANTunde_xunde_a) (t. ((a_CONSTANTunde_yunde_a) (TLA.in a_CONSTANTunde_yunde_a
a_CONSTANTunde_xunde_a)))))
(TLA.FuncSet a_CONSTANTunde_aunde_a (TLA.UNION a_CONSTANTunde_aunde_a)))
$goal (TLA.bEx (TLA.FuncSet a_CONSTANTunde_aunde_a (TLA.UNION a_CONSTANTunde_aunde_a)) ((a_CONSTANTunde_funde_a) (TLA.bAll a_CONSTANTunde_aunde_a ((a_CONSTANTunde_xunde_a) (TLA.in (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a)
a_CONSTANTunde_xunde_a)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"bAll(a_CONSTANTunde_aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. ((Fcn(a_CONSTANTunde_aunde_a, (\<lambda>a_CONSTANTunde_xunde_a_1. (CHOOSE a_CONSTANTunde_yunde_a:(a_CONSTANTunde_yunde_a \\in a_CONSTANTunde_xunde_a_1))))[a_CONSTANTunde_xunde_a]) \\in a_CONSTANTunde_xunde_a)))" (is "?z_ha")
 using v'14 by blast
 have z_Hb:"(Fcn(a_CONSTANTunde_aunde_a, (\<lambda>a_CONSTANTunde_xunde_a_1. (CHOOSE a_CONSTANTunde_yunde_a:(a_CONSTANTunde_yunde_a \\in a_CONSTANTunde_xunde_a_1)))) \\in FuncSet(a_CONSTANTunde_aunde_a, UNION(a_CONSTANTunde_aunde_a)))" (is "?z_hb")
 using v'15 by blast
 assume z_Hc:"(~bEx(FuncSet(a_CONSTANTunde_aunde_a, UNION(a_CONSTANTunde_aunde_a)), (\<lambda>a_CONSTANTunde_funde_a. bAll(a_CONSTANTunde_aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. ((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]) \\in a_CONSTANTunde_xunde_a))))))" (is "~?z_hq")
 have z_Hx_z_Hc: "(~(\\E x:((x \\in FuncSet(a_CONSTANTunde_aunde_a, UNION(a_CONSTANTunde_aunde_a)))&bAll(a_CONSTANTunde_aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. ((x[a_CONSTANTunde_xunde_a]) \\in a_CONSTANTunde_xunde_a)))))) == (~?z_hq)" (is "?z_hx == ?z_hc")
 by (unfold bEx_def)
 have z_Hx: "?z_hx" (is "~(\\E x : ?z_hbg(x))")
 by (unfold z_Hx_z_Hc, fact z_Hc)
 have z_Hbh: "~?z_hbg(Fcn(a_CONSTANTunde_aunde_a, (\<lambda>a_CONSTANTunde_xunde_a_1. (CHOOSE a_CONSTANTunde_yunde_a:(a_CONSTANTunde_yunde_a \\in a_CONSTANTunde_xunde_a_1)))))"
 by (rule zenon_notex_0 [of "?z_hbg" "Fcn(a_CONSTANTunde_aunde_a, (\<lambda>a_CONSTANTunde_xunde_a_1. (CHOOSE a_CONSTANTunde_yunde_a:(a_CONSTANTunde_yunde_a \\in a_CONSTANTunde_xunde_a_1))))", OF z_Hx])
 show FALSE
 proof (rule zenon_notand [OF z_Hbh])
  assume z_Hbi:"(~?z_hb)"
  show FALSE
  by (rule notE [OF z_Hbi z_Hb])
 next
  assume z_Hbj:"(~?z_ha)"
  show FALSE
  by (rule notE [OF z_Hbj z_Ha])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 10"; *} qed
end

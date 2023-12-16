(* automatically generated -- do not edit manually *)
theory higher_order_statement_test imports Constant Zenon begin
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

lemma ob'8:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefConclusion_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_factorial_ suppressed *)
assumes v'12: "((a_CONSTANTunde_NatInductiveDefHypothesisunde_a ((a_CONSTANTunde_factorialunde_a), ((Succ[0])), (\<lambda> a_Unknownunde_vunde_a a_Unknownunde_nunde_a . ((mult ((a_Unknownunde_nunde_a), (a_Unknownunde_vunde_a))))))))"
assumes v'13: "((\<And> a_CONSTANTunde_Defunde_a :: c => c => c. (\<forall>a_CONSTANTunde_funde_a : (\<forall>a_CONSTANTunde_f0unde_a : ((((a_CONSTANTunde_NatInductiveDefHypothesisunde_a ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_f0unde_a), (a_CONSTANTunde_Defunde_a)))) \<Rightarrow> ((a_CONSTANTunde_NatInductiveDefConclusionunde_a ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_f0unde_a), (a_CONSTANTunde_Defunde_a))))))))))"
shows "((a_CONSTANTunde_NatInductiveDefConclusionunde_a ((a_CONSTANTunde_factorialunde_a), ((Succ[0])), (\<lambda> a_Unknownunde_vunde_a a_Unknownunde_nunde_a . ((mult ((a_Unknownunde_nunde_a), (a_Unknownunde_vunde_a))))))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"

(* BEGIN ZENON INPUT
;; file=.tlacache/higher_order_statement_test.tlaps/tlapm_906c54.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/higher_order_statement_test.tlaps/tlapm_906c54.znn.out
;; obligation #8
$hyp "v'12" (a_CONSTANTunde_NatInductiveDefHypothesisunde_a a_CONSTANTunde_factorialunde_a
(TLA.fapply TLA.Succ 0)
((a_Unknownunde_vunde_a a_Unknownunde_nunde_a ) (arith.mul a_Unknownunde_nunde_a
a_Unknownunde_vunde_a)))
$hyp "v'13" (A. ((a_CONSTANTunde_Defunde_a) (A. ((a_CONSTANTunde_funde_a) (A. ((a_CONSTANTunde_f0unde_a) (=> (a_CONSTANTunde_NatInductiveDefHypothesisunde_a a_CONSTANTunde_funde_a
a_CONSTANTunde_f0unde_a a_CONSTANTunde_Defunde_a)
(a_CONSTANTunde_NatInductiveDefConclusionunde_a a_CONSTANTunde_funde_a
a_CONSTANTunde_f0unde_a
a_CONSTANTunde_Defunde_a))))))))
$goal (a_CONSTANTunde_NatInductiveDefConclusionunde_a a_CONSTANTunde_factorialunde_a
(TLA.fapply TLA.Succ 0)
((a_Unknownunde_vunde_a a_Unknownunde_nunde_a ) (arith.mul a_Unknownunde_nunde_a
a_Unknownunde_vunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"(\\A a_CONSTANTunde_Defunde_a:(\\A a_CONSTANTunde_funde_a:(\\A a_CONSTANTunde_f0unde_a:(a_CONSTANTunde_NatInductiveDefHypothesisunde_a(a_CONSTANTunde_funde_a, a_CONSTANTunde_f0unde_a, a_CONSTANTunde_Defunde_a)=>a_CONSTANTunde_NatInductiveDefConclusionunde_a(a_CONSTANTunde_funde_a, a_CONSTANTunde_f0unde_a, a_CONSTANTunde_Defunde_a)))))" (is "\\A x : ?z_hl(x)")
 using v'13 by blast
 have z_Ha:"a_CONSTANTunde_NatInductiveDefHypothesisunde_a(a_CONSTANTunde_factorialunde_a, 1, (\<lambda>a_Unknownunde_vunde_a. (\<lambda>a_Unknownunde_nunde_a. (a_Unknownunde_nunde_a * a_Unknownunde_vunde_a))))" (is "?z_ha")
 using v'12 by blast
 assume z_Hc:"(~a_CONSTANTunde_NatInductiveDefConclusionunde_a(a_CONSTANTunde_factorialunde_a, 1, (\<lambda>a_Unknownunde_vunde_a. (\<lambda>a_Unknownunde_nunde_a. (a_Unknownunde_nunde_a * a_Unknownunde_vunde_a)))))" (is "~?z_ht")
 have z_Hu: "?z_hl((\<lambda>a_Unknownunde_vunde_a. (\<lambda>a_Unknownunde_nunde_a. (a_Unknownunde_nunde_a * a_Unknownunde_vunde_a))))" (is "\\A x : ?z_hv(x)")
 by (rule zenon_all_0 [of "?z_hl" "(\<lambda>a_Unknownunde_vunde_a. (\<lambda>a_Unknownunde_nunde_a. (a_Unknownunde_nunde_a * a_Unknownunde_vunde_a)))", OF z_Hb])
 have z_Hw: "?z_hv(a_CONSTANTunde_factorialunde_a)" (is "\\A x : ?z_hx(x)")
 by (rule zenon_all_0 [of "?z_hv" "a_CONSTANTunde_factorialunde_a", OF z_Hu])
 have z_Hy: "?z_hx(1)"
 by (rule zenon_all_0 [of "?z_hx" "1", OF z_Hw])
 show FALSE
 proof (rule zenon_imply [OF z_Hy])
  assume z_Hz:"(~?z_ha)"
  show FALSE
  by (rule notE [OF z_Hz z_Ha])
 next
  assume z_Ht:"?z_ht"
  show FALSE
  by (rule notE [OF z_Hc z_Ht])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
lemma ob'1:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_factorial_ suppressed *)
assumes v'10: "(((a_CONSTANTunde_factorialunde_a) = ([ a_CONSTANTunde_iunde_a \<in> (Nat)  \<mapsto> (cond((((a_CONSTANTunde_iunde_a) = ((0)))), ((Succ[0])), ((mult ((a_CONSTANTunde_iunde_a), (fapply ((a_CONSTANTunde_factorialunde_a), ((arith_add ((a_CONSTANTunde_iunde_a), ((minus (((Succ[0])))))))))))))))])))"
shows "(\<forall> a_CONSTANTunde_nunde_a \<in> (Nat) : (((fapply ((a_CONSTANTunde_factorialunde_a), (a_CONSTANTunde_nunde_a))) = (cond((((a_CONSTANTunde_nunde_a) = ((0)))), ((Succ[0])), ((mult ((a_CONSTANTunde_nunde_a), (fapply ((a_CONSTANTunde_factorialunde_a), ((arith_add ((a_CONSTANTunde_nunde_a), ((minus (((Succ[0]))))))))))))))))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/higher_order_statement_test.tlaps/tlapm_7a3e66.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/higher_order_statement_test.tlaps/tlapm_7a3e66.znn.out
;; obligation #1
$hyp "v'10" (= a_CONSTANTunde_factorialunde_a
(TLA.Fcn arith.N ((a_CONSTANTunde_iunde_a) (TLA.cond (= a_CONSTANTunde_iunde_a
0) (TLA.fapply TLA.Succ 0) (arith.mul a_CONSTANTunde_iunde_a
(TLA.fapply a_CONSTANTunde_factorialunde_a (arith.add a_CONSTANTunde_iunde_a
(arith.minus (TLA.fapply TLA.Succ 0)))))))))
$goal (TLA.bAll arith.N ((a_CONSTANTunde_nunde_a) (= (TLA.fapply a_CONSTANTunde_factorialunde_a a_CONSTANTunde_nunde_a)
(TLA.cond (= a_CONSTANTunde_nunde_a
0) (TLA.fapply TLA.Succ 0) (arith.mul a_CONSTANTunde_nunde_a
(TLA.fapply a_CONSTANTunde_factorialunde_a (arith.add a_CONSTANTunde_nunde_a
(arith.minus (TLA.fapply TLA.Succ 0)))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(a_CONSTANTunde_factorialunde_a=Fcn(Nat, (\<lambda>a_CONSTANTunde_iunde_a. cond((a_CONSTANTunde_iunde_a=0), 1, (a_CONSTANTunde_iunde_a * (a_CONSTANTunde_factorialunde_a[(a_CONSTANTunde_iunde_a +  -.(1))]))))))" (is "_=?z_hd")
 using v'10 by blast
 assume z_Hb:"(~bAll(Nat, (\<lambda>a_CONSTANTunde_nunde_a. ((a_CONSTANTunde_factorialunde_a[a_CONSTANTunde_nunde_a])=cond((a_CONSTANTunde_nunde_a=0), 1, (a_CONSTANTunde_nunde_a * (a_CONSTANTunde_factorialunde_a[(a_CONSTANTunde_nunde_a +  -.(1))])))))))" (is "~?z_hp")
 have z_Hz_z_Hb: "(~(\\A x:((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))]))))))) == (~?z_hp)" (is "?z_hz == ?z_hb")
 by (unfold bAll_def)
 have z_Hz: "?z_hz" (is "~(\\A x : ?z_hbl(x))")
 by (unfold z_Hz_z_Hb, fact z_Hb)
 have z_Hbm: "(\\E x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))])))))))" (is "\\E x : ?z_hbo(x)")
 by (rule zenon_notallex_0 [of "?z_hbl", OF z_Hz])
 have z_Hbp: "?z_hbo((CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))]))))))))" (is "~(?z_hbr=>?z_hbs)")
 by (rule zenon_ex_choose_0 [of "?z_hbo", OF z_Hbm])
 have z_Hbr: "?z_hbr"
 by (rule zenon_notimply_0 [OF z_Hbp])
 have z_Hbt: "((a_CONSTANTunde_factorialunde_a[(CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))])))))))])~=cond(((CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))])))))))=0), 1, ((CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))]))))))) * (a_CONSTANTunde_factorialunde_a[((CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))]))))))) +  -.(1))]))))" (is "?z_hbu~=?z_hbv")
 by (rule zenon_notimply_1 [OF z_Hbp])
 have z_Hca: "(((isAFcn(a_CONSTANTunde_factorialunde_a)<=>isAFcn(?z_hd))&(DOMAIN(a_CONSTANTunde_factorialunde_a)=DOMAIN(?z_hd)))&(\\A zenon_Vh:((a_CONSTANTunde_factorialunde_a[zenon_Vh])=(?z_hd[zenon_Vh]))))" (is "?z_hcb&?z_hci")
 by (rule zenon_funequal_0 [of "a_CONSTANTunde_factorialunde_a" "?z_hd", OF z_Ha])
 have z_Hci: "?z_hci" (is "\\A x : ?z_hcn(x)")
 by (rule zenon_and_1 [OF z_Hca])
 have z_Hco: "?z_hcn((CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))]))))))))" (is "_=?z_hcp")
 by (rule zenon_all_0 [of "?z_hcn" "(CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))])))))))", OF z_Hci])
 show FALSE
 proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vxa. (?z_hbu=zenon_Vxa))" "Nat" "(\<lambda>a_CONSTANTunde_iunde_a. cond((a_CONSTANTunde_iunde_a=0), 1, (a_CONSTANTunde_iunde_a * (a_CONSTANTunde_factorialunde_a[(a_CONSTANTunde_iunde_a +  -.(1))]))))" "(CHOOSE x:(~((x \\in Nat)=>((a_CONSTANTunde_factorialunde_a[x])=cond((x=0), 1, (x * (a_CONSTANTunde_factorialunde_a[(x +  -.(1))])))))))", OF z_Hco])
  assume z_Hct:"(~?z_hbr)"
  show FALSE
  by (rule notE [OF z_Hct z_Hbr])
 next
  assume z_Hbs:"?z_hbs"
  show FALSE
  by (rule notE [OF z_Hbt z_Hbs])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

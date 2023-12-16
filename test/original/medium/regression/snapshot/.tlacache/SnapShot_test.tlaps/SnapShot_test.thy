(* automatically generated -- do not edit manually *)
theory SnapShot_test imports Constant Zenon begin
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

lemma ob'93:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'53: "(((a_VARIABLEunde_resultunde_a) = ([ a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'54: "(((a_VARIABLEunde_A2unde_a) = ([ a_CONSTANTunde_iunde_a \<in> (Nat)  \<mapsto> ({})])))"
assumes v'55: "(((a_VARIABLEunde_A3unde_a) = ([ a_CONSTANTunde_iunde_a \<in> (Nat)  \<mapsto> ({})])))"
assumes v'56: "(((a_VARIABLEunde_myValsunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'57: "(((a_VARIABLEunde_knownunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'58: "(((a_VARIABLEunde_notKnownunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'59: "(((a_VARIABLEunde_lnbpartunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ((0))])))"
assumes v'60: "(((a_VARIABLEunde_nbpartunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ((0))])))"
assumes v'61: "(((a_VARIABLEunde_nextoutunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'62: "(((a_VARIABLEunde_outunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'63: "(((a_VARIABLEunde_pcunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (''a'')])))"
assumes v'73: "(\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> ((a_CONSTANTunde_PUnionunde_a ((a_VARIABLEunde_myValsunde_a)))))) & (((fapply ((a_VARIABLEunde_outunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_punde_a))))) & (((fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''e''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))))))) & ((leq ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))) & ((leq ((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a))), (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))))) & ((((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''e''))) & (((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))) \<Rightarrow> (((fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))))) & (((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Rightarrow> (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) \<noteq> (''a''))))) & (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) \<noteq> (''a''))) \<Rightarrow> ((((a_CONSTANTunde_punde_a) \<in> (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))))) & (((fapply ((a_VARIABLEunde_A2unde_a), ((arith_add (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))), ((minus (((Succ[0])))))))))) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))))))))))"
assumes v'74: "((((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A3unde_a)))) \<subseteq> ((a_CONSTANTunde_PUnionunde_a ((a_VARIABLEunde_myValsunde_a))))))"
assumes v'75: "(\<forall> a_CONSTANTunde_iunde_a \<in> (Nat) : ((((fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a))) = ({}))) | (\<exists> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) \<noteq> (''a''))) & (((a_CONSTANTunde_iunde_a) = ((arith_add (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))), ((minus (((Succ[0])))))))))) & (((fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a))) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))))))"
shows "((\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> ((a_CONSTANTunde_PUnionunde_a ((a_VARIABLEunde_myValsunde_a)))))) & (((fapply ((a_VARIABLEunde_outunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_punde_a))))) & (((fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''e''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))))))) & ((leq ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))) & ((leq ((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a))), (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))))) & ((((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''e''))) & (((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))) \<Rightarrow> (((fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))))) & (((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Rightarrow> (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) \<noteq> (''a''))))) & (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) \<noteq> (''a''))) \<Rightarrow> ((((a_CONSTANTunde_punde_a) \<in> (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))))) & (((fapply ((a_VARIABLEunde_A2unde_a), ((arith_add (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))), ((minus (((Succ[0])))))))))) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))))))) & ((((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A3unde_a)))) \<subseteq> ((a_CONSTANTunde_PUnionunde_a ((a_VARIABLEunde_myValsunde_a)))))) & (\<forall> a_CONSTANTunde_iunde_a \<in> (Nat) : ((((fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a))) = ({}))) | (\<exists> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) \<noteq> (''a''))) & (((a_CONSTANTunde_iunde_a) = ((arith_add (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))), ((minus (((Succ[0])))))))))) & (((fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a))) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))))))))))"(is "PROP ?ob'93")
proof -
ML_command {* writeln "*** TLAPS ENTER 93"; *}
show "PROP ?ob'93"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_784e62.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_784e62.znn.out
;; obligation #93
$hyp "v'53" (= a_VARIABLEunde_resultunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) TLA.emptyset)))
$hyp "v'54" (= a_VARIABLEunde_A2unde_a
(TLA.Fcn arith.N ((a_CONSTANTunde_iunde_a) TLA.emptyset)))
$hyp "v'55" (= a_VARIABLEunde_A3unde_a
(TLA.Fcn arith.N ((a_CONSTANTunde_iunde_a) TLA.emptyset)))
$hyp "v'56" (= a_VARIABLEunde_myValsunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'57" (= a_VARIABLEunde_knownunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'58" (= a_VARIABLEunde_notKnownunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'59" (= a_VARIABLEunde_lnbpartunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) 0)))
$hyp "v'60" (= a_VARIABLEunde_nbpartunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) 0)))
$hyp "v'61" (= a_VARIABLEunde_nextoutunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'62" (= a_VARIABLEunde_outunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'63" (= a_VARIABLEunde_pcunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) "a")))
$hyp "v'73" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (TLA.subseteq (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_PUnionunde_a a_VARIABLEunde_myValsunde_a))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_outunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "e")
(= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(arith.le (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a)))
(arith.le (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a))
(=> (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "e")
(= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))))
(= (TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(=> (-. (= (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))
(-. (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "a")))
(=> (-. (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "a"))
(/\ (TLA.in a_CONSTANTunde_punde_a
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(= (TLA.fapply a_VARIABLEunde_A2unde_a (arith.add (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(arith.minus (TLA.fapply TLA.Succ 0))))
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)))))))
$hyp "v'74" (TLA.subseteq (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A3unde_a)
(a_CONSTANTunde_PUnionunde_a a_VARIABLEunde_myValsunde_a))
$hyp "v'75" (TLA.bAll arith.N ((a_CONSTANTunde_iunde_a) (\/ (= (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)
TLA.emptyset)
(TLA.bEx a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (-. (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")) (= a_CONSTANTunde_iunde_a
(arith.add (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(arith.minus (TLA.fapply TLA.Succ 0))))
(= (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))))))))
$goal (/\ (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (TLA.subseteq (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_PUnionunde_a a_VARIABLEunde_myValsunde_a))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_outunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "e")
(= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(arith.le (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a)))
(arith.le (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a))
(=> (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "e")
(= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))))
(= (TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(=> (-. (= (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))
(-. (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "a")))
(=> (-. (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "a"))
(/\ (TLA.in a_CONSTANTunde_punde_a
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(= (TLA.fapply a_VARIABLEunde_A2unde_a (arith.add (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(arith.minus (TLA.fapply TLA.Succ 0))))
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)))))))
(TLA.subseteq (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A3unde_a)
(a_CONSTANTunde_PUnionunde_a a_VARIABLEunde_myValsunde_a))
(TLA.bAll arith.N ((a_CONSTANTunde_iunde_a) (\/ (= (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)
TLA.emptyset)
(TLA.bEx a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (-. (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")) (= a_CONSTANTunde_iunde_a
(arith.add (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(arith.minus (TLA.fapply TLA.Succ 0))))
(= (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hl:"bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\subseteq a_CONSTANTunde_PUnionunde_a(a_VARIABLEunde_myValsunde_a))&(((a_VARIABLEunde_outunde_a[a_CONSTANTunde_punde_a]) \\subseteq (a_VARIABLEunde_nextoutunde_a[a_CONSTANTunde_punde_a]))&(((a_VARIABLEunde_nextoutunde_a[a_CONSTANTunde_punde_a]) \\subseteq (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))&((((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''e'')=>((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])))&(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]) <= a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a)))&(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a]) <= (a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]))&(((((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''e'')&((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))))=>((a_VARIABLEunde_nextoutunde_a[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a])))&(((a_VARIABLEunde_myValsunde_a[a_CONSTANTunde_punde_a]) \\subseteq (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))&((((a_VARIABLEunde_myValsunde_a[a_CONSTANTunde_punde_a])~={})=>((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])~=''a''))&(((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])~=''a'')=>((a_CONSTANTunde_punde_a \\in (a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a]))&((a_VARIABLEunde_A2unde_a[(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])) +  -.(1))])=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])))))))))))))))" (is "?z_hl")
 using v'73 by blast
 have z_Hm:"(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A3unde_a) \\subseteq a_CONSTANTunde_PUnionunde_a(a_VARIABLEunde_myValsunde_a))" (is "?z_hm")
 using v'74 by blast
 have z_Hn:"bAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (((a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])={})|bEx(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])~=''a'')&((a_CONSTANTunde_iunde_a=(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])) +  -.(1)))&((a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])))))))))" (is "?z_hn")
 using v'75 by blast
 assume z_Ho:"(~(?z_hl&(?z_hm&?z_hn)))" (is "~(_&?z_hdm)")
 show FALSE
 proof (rule zenon_notand [OF z_Ho])
  assume z_Hdn:"(~?z_hl)"
  show FALSE
  by (rule notE [OF z_Hdn z_Hl])
 next
  assume z_Hdo:"(~?z_hdm)"
  show FALSE
  proof (rule zenon_notand [OF z_Hdo])
   assume z_Hdp:"(~?z_hm)"
   show FALSE
   by (rule notE [OF z_Hdp z_Hm])
  next
   assume z_Hdq:"(~?z_hn)"
   show FALSE
   by (rule notE [OF z_Hdq z_Hn])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 93"; *} qed
lemma ob'131:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'51: "(((a_VARIABLEunde_resultunde_a) = ([ a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'52: "(((a_VARIABLEunde_A2unde_a) = ([ a_CONSTANTunde_iunde_a \<in> (Nat)  \<mapsto> ({})])))"
assumes v'53: "(((a_VARIABLEunde_A3unde_a) = ([ a_CONSTANTunde_iunde_a \<in> (Nat)  \<mapsto> ({})])))"
assumes v'54: "(((a_VARIABLEunde_myValsunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'55: "(((a_VARIABLEunde_knownunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'56: "(((a_VARIABLEunde_notKnownunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'57: "(((a_VARIABLEunde_lnbpartunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ((0))])))"
assumes v'58: "(((a_VARIABLEunde_nbpartunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ((0))])))"
assumes v'59: "(((a_VARIABLEunde_nextoutunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'60: "(((a_VARIABLEunde_outunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> ({})])))"
assumes v'61: "(((a_VARIABLEunde_pcunde_a) = ([ a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (''a'')])))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'81: "(\<forall> a_CONSTANTunde_iunde_a \<in> (Nat) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))) \<in> ({((0)), ((arith_add ((a_CONSTANTunde_iunde_a), ((Succ[0])))))}))))"
assumes v'82: "((((a_CONSTANTunde_Cardinalityunde_a (({})))) = ((0))))"
shows "((((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))) = ((0))))"(is "PROP ?ob'131")
proof -
ML_command {* writeln "*** TLAPS ENTER 131"; *}
show "PROP ?ob'131"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_70434d.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_70434d.znn.out
;; obligation #131
$hyp "v'51" (= a_VARIABLEunde_resultunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) TLA.emptyset)))
$hyp "v'52" (= a_VARIABLEunde_A2unde_a
(TLA.Fcn arith.N ((a_CONSTANTunde_iunde_a) TLA.emptyset)))
$hyp "v'53" (= a_VARIABLEunde_A3unde_a
(TLA.Fcn arith.N ((a_CONSTANTunde_iunde_a) TLA.emptyset)))
$hyp "v'54" (= a_VARIABLEunde_myValsunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'55" (= a_VARIABLEunde_knownunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'56" (= a_VARIABLEunde_notKnownunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'57" (= a_VARIABLEunde_lnbpartunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) 0)))
$hyp "v'58" (= a_VARIABLEunde_nbpartunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) 0)))
$hyp "v'59" (= a_VARIABLEunde_nextoutunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'60" (= a_VARIABLEunde_outunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) TLA.emptyset)))
$hyp "v'61" (= a_VARIABLEunde_pcunde_a
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) "a")))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'81" (TLA.bAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a))
(TLA.set 0 (arith.add a_CONSTANTunde_iunde_a
(TLA.fapply TLA.Succ 0))))))
$hyp "v'82" (= (a_CONSTANTunde_Cardinalityunde_a TLA.emptyset)
0)
$goal (= (a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))
0)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hb:"(a_VARIABLEunde_A2unde_a=Fcn(Nat, (\<lambda>a_CONSTANTunde_punde_a. {})))" (is "_=?z_hq")
 using v'52 by blast
 have z_Hn:"(a_CONSTANTunde_Cardinalityunde_a({})=0)" (is "?z_hu=_")
 using v'82 by blast
 assume z_Ho:"(a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))~=0)" (is "?z_hw~=_")
 have z_Hbc: "(?z_hw~=?z_hu)"
 by (rule ssubst [where P="(\<lambda>zenon_Vf. (?z_hw~=zenon_Vf))", OF z_Hn z_Ho])
 show FALSE
 proof (rule zenon_noteq [of "?z_hu"])
  have z_Hbg: "(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))={})" (is "?z_hx=_")
  proof (rule zenon_nnpp [of "(?z_hx={})"])
   assume z_Hbh:"(?z_hx~={})"
   have z_Hbi: "(~(\\A zenon_Vm:((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {}))))" (is "~(\\A x : ?z_hbo(x))")
   by (rule zenon_notsetequal_0 [of "?z_hx" "{}", OF z_Hbh])
   have z_Hbp: "(\\E zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {}))))" (is "\\E x : ?z_hbr(x)")
   by (rule zenon_notallex_0 [of "?z_hbo", OF z_Hbi])
   have z_Hbs: "?z_hbr((CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {})))))" (is "~(?z_hbu<=>?z_hbv)")
   by (rule zenon_ex_choose_0 [of "?z_hbr", OF z_Hbp])
   show FALSE
   proof (rule zenon_notequiv [OF z_Hbs])
    assume z_Hbw:"(~?z_hbu)"
    assume z_Hbv:"?z_hbv"
    show FALSE
    by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {}))))", OF z_Hbv])
   next
    assume z_Hbu:"?z_hbu"
    assume z_Hbx:"(~?z_hbv)"
    have z_Hby: "(\\E zenon_Vpa:((zenon_Vpa \\in setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))&((CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {})))) \\in zenon_Vpa)))" (is "\\E x : ?z_hcd(x)")
    by (rule zenon_in_UNION_0 [of "(CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {}))))" "setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))", OF z_Hbu])
    have z_Hce: "?z_hcd((CHOOSE zenon_Vpa:((zenon_Vpa \\in setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))&((CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {})))) \\in zenon_Vpa))))" (is "?z_hcg&?z_hch")
    by (rule zenon_ex_choose_0 [of "?z_hcd", OF z_Hby])
    have z_Hcg: "?z_hcg"
    by (rule zenon_and_0 [OF z_Hce])
    have z_Hch: "?z_hch"
    by (rule zenon_and_1 [OF z_Hce])
    have z_Hci: "(\\E zenon_Vwa:((zenon_Vwa \\in Nat)&((CHOOSE zenon_Vpa:((zenon_Vpa \\in setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))&((CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {})))) \\in zenon_Vpa)))=(a_VARIABLEunde_A2unde_a[zenon_Vwa]))))" (is "\\E x : ?z_hco(x)")
    by (rule zenon_in_setofall_0 [of "(CHOOSE zenon_Vpa:((zenon_Vpa \\in setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))&((CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {})))) \\in zenon_Vpa)))" "Nat" "(\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))", OF z_Hcg])
    have z_Hcp: "?z_hco((CHOOSE zenon_Vwa:((zenon_Vwa \\in Nat)&((CHOOSE zenon_Vpa:((zenon_Vpa \\in setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))&((CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {})))) \\in zenon_Vpa)))=(a_VARIABLEunde_A2unde_a[zenon_Vwa])))))" (is "?z_hcr&?z_hcs")
    by (rule zenon_ex_choose_0 [of "?z_hco", OF z_Hci])
    have z_Hcr: "?z_hcr"
    by (rule zenon_and_0 [OF z_Hcp])
    have z_Hcs: "?z_hcs" (is "?z_hcf=?z_hct")
    by (rule zenon_and_1 [OF z_Hcp])
    have z_Hcu: "(?z_hcf=(?z_hq[(CHOOSE zenon_Vwa:((zenon_Vwa \\in Nat)&(?z_hcf=(a_VARIABLEunde_A2unde_a[zenon_Vwa]))))]))" (is "_=?z_hcv")
    by (rule subst [where P="(\<lambda>zenon_Vfc. (?z_hcf=(zenon_Vfc[(CHOOSE zenon_Vwa:((zenon_Vwa \\in Nat)&(?z_hcf=(a_VARIABLEunde_A2unde_a[zenon_Vwa]))))])))", OF z_Hb z_Hcs])
    show FALSE
    proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vfc. (?z_hcf=zenon_Vfc))" "Nat" "(\<lambda>a_CONSTANTunde_punde_a. {})" "(CHOOSE zenon_Vwa:((zenon_Vwa \\in Nat)&(?z_hcf=(a_VARIABLEunde_A2unde_a[zenon_Vwa]))))", OF z_Hcu])
     assume z_Hdc:"(~?z_hcr)"
     show FALSE
     by (rule notE [OF z_Hdc z_Hcr])
    next
     assume z_Hdd:"(?z_hcf={})"
     have z_Hde: "(\\A zenon_Vkc:(~(zenon_Vkc \\in ?z_hcf)))" (is "\\A x : ?z_hdi(x)")
     by (rule zenon_setequalempty_0 [of "?z_hcf", OF z_Hdd])
     have z_Hdj: "?z_hdi((CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {})))))"
     by (rule zenon_all_0 [of "?z_hdi" "(CHOOSE zenon_Vm:(~((zenon_Vm \\in ?z_hx)<=>(zenon_Vm \\in {}))))", OF z_Hde])
     show FALSE
     by (rule notE [OF z_Hdj z_Hch])
    qed
   qed
  qed
  have z_Hdk: "(?z_hu~=?z_hu)"
  by (rule subst [where P="(\<lambda>zenon_Vk. (a_CONSTANTunde_Cardinalityunde_a(zenon_Vk)~=?z_hu))", OF z_Hbg], fact z_Hbc)
  thus "(?z_hu~=?z_hu)" .
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 131"; *} qed
lemma ob'658:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'54: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'55: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'68: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'69: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'70: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'71: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'72: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'73: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'74: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'75: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'76: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'77: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'78: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h0806c :: c)))"
assumes v'92: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({})))"
shows "((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c''))) & ((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a))) & (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) & ((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a))) & ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a))) & ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'658")
proof -
ML_command {* writeln "*** TLAPS ENTER 658"; *}
show "PROP ?ob'658"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_0defb0.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_0defb0.znn.out
;; obligation #658
$hyp "v'54" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'55" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'68" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'69" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'70" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'71" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'72" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'73" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'74" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'75" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'76" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'77" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'78" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h0806c)
$hyp "v'92" (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset))
$goal (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "c")
(= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)
(/\ (= a_VARIABLEunde_resultunde_hash_primea a_VARIABLEunde_resultunde_a)
(= a_VARIABLEunde_A2unde_hash_primea a_VARIABLEunde_A2unde_a)
(= a_VARIABLEunde_A3unde_hash_primea a_VARIABLEunde_A3unde_a)
(= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_nbpartunde_hash_primea a_VARIABLEunde_nbpartunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''c'')" (is "?z_hs=?z_hv")
 using v'69 by blast
 have z_Hf:"(a_VARIABLEunde_lnbpartunde_hash_primea=except(a_VARIABLEunde_lnbpartunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])))" (is "_=?z_hx")
 using v'70 by blast
 have z_Hg:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hbc")
 using v'71 by blast
 have z_Hh:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, ((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]) +  -.(1))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hbo")
 using v'72 by blast
 have z_Hq:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hbz~=_")
 using v'92 by blast
 have z_Hd:"cond((?z_hbz~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)), (cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))))" (is "?z_hd")
 using v'68 by blast
 have z_Hi:"(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)"
 using v'73 by blast
 have z_Hj:"(a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)"
 using v'74 by blast
 have z_Hk:"(a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)"
 using v'75 by blast
 have z_Hl:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'76 by blast
 have z_Hm:"(a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)"
 using v'77 by blast
 have z_Hn:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'78 by blast
 assume z_Hr:"(~((?z_hs=?z_hv)&((a_VARIABLEunde_lnbpartunde_hash_primea=?z_hx)&((a_VARIABLEunde_knownunde_hash_primea=?z_hbc)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbo)&((?z_hbz~={})&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&((a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)&((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)&((a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)&((a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)&((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&((a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a))))))))))))))" (is "~(?z_he&?z_hdj)")
 show FALSE
 proof (rule zenon_notand [OF z_Hr])
  assume z_Hdu:"(?z_hs~=?z_hv)"
  show FALSE
  by (rule notE [OF z_Hdu z_He])
 next
  assume z_Hdv:"(~?z_hdj)" (is "~(?z_hf&?z_hdk)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdv])
   assume z_Hdw:"(a_VARIABLEunde_lnbpartunde_hash_primea~=?z_hx)"
   show FALSE
   by (rule notE [OF z_Hdw z_Hf])
  next
   assume z_Hdx:"(~?z_hdk)" (is "~(?z_hg&?z_hdl)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdx])
    assume z_Hdy:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbc)"
    show FALSE
    by (rule notE [OF z_Hdy z_Hg])
   next
    assume z_Hdz:"(~?z_hdl)" (is "~(?z_hh&?z_hdm)")
    show FALSE
    proof (rule zenon_notand [OF z_Hdz])
     assume z_Hea:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbo)"
     show FALSE
     by (rule notE [OF z_Hea z_Hh])
    next
     assume z_Heb:"(~?z_hdm)" (is "~(?z_hq&?z_hdn)")
     show FALSE
     proof (rule zenon_notand [OF z_Heb])
      assume z_Hec:"(~?z_hq)" (is "~~?z_hed")
      show FALSE
      by (rule notE [OF z_Hec z_Hq])
     next
      assume z_Hee:"(~?z_hdn)" (is "~(?z_hcc&?z_hdo)")
      show FALSE
      proof (rule zenon_notand [OF z_Hee])
       assume z_Hef:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))" (is "_~=?z_hce")
       show FALSE
       proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hq" "(?z_hcc&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" "(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
        assume z_Hq:"?z_hq"
        assume z_Hcb:"(?z_hcc&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "_&?z_hcg")
        have z_Hcc: "?z_hcc"
        by (rule zenon_and_0 [OF z_Hcb])
        show FALSE
        by (rule notE [OF z_Hef z_Hcc])
       next
        assume z_Hec:"(~?z_hq)" (is "~~?z_hed")
        assume z_Hcj:"(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hck&?z_hcw")
        show FALSE
        by (rule notE [OF z_Hec z_Hq])
       qed
      next
       assume z_Hei:"(~?z_hdo)" (is "~(?z_hcg&?z_hdp)")
       show FALSE
       proof (rule zenon_notand [OF z_Hei])
        assume z_Hej:"(a_VARIABLEunde_nextoutunde_hash_primea~=a_VARIABLEunde_nextoutunde_a)"
        show FALSE
        proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hq" "(?z_hcc&?z_hcg)" "(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hcg))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
         assume z_Hq:"?z_hq"
         assume z_Hcb:"(?z_hcc&?z_hcg)"
         have z_Hcg: "?z_hcg"
         by (rule zenon_and_1 [OF z_Hcb])
         show FALSE
         by (rule notE [OF z_Hej z_Hcg])
        next
         assume z_Hec:"(~?z_hq)" (is "~~?z_hed")
         assume z_Hcj:"(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hcg))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hck&?z_hcw")
         show FALSE
         by (rule notE [OF z_Hec z_Hq])
        qed
       next
        assume z_Hek:"(~?z_hdp)" (is "~(?z_hi&?z_hdq)")
        show FALSE
        proof (rule zenon_notand [OF z_Hek])
         assume z_Hel:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
         show FALSE
         by (rule notE [OF z_Hel z_Hi])
        next
         assume z_Hem:"(~?z_hdq)" (is "~(?z_hj&?z_hdr)")
         show FALSE
         proof (rule zenon_notand [OF z_Hem])
          assume z_Hen:"(a_VARIABLEunde_A2unde_hash_primea~=a_VARIABLEunde_A2unde_a)"
          show FALSE
          by (rule notE [OF z_Hen z_Hj])
         next
          assume z_Heo:"(~?z_hdr)" (is "~(?z_hk&?z_hds)")
          show FALSE
          proof (rule zenon_notand [OF z_Heo])
           assume z_Hep:"(a_VARIABLEunde_A3unde_hash_primea~=a_VARIABLEunde_A3unde_a)"
           show FALSE
           by (rule notE [OF z_Hep z_Hk])
          next
           assume z_Heq:"(~?z_hds)" (is "~(?z_hl&?z_hdt)")
           show FALSE
           proof (rule zenon_notand [OF z_Heq])
            assume z_Her:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
            show FALSE
            by (rule notE [OF z_Her z_Hl])
           next
            assume z_Hes:"(~?z_hdt)" (is "~(?z_hm&?z_hn)")
            show FALSE
            proof (rule zenon_notand [OF z_Hes])
             assume z_Het:"(a_VARIABLEunde_nbpartunde_hash_primea~=a_VARIABLEunde_nbpartunde_a)"
             show FALSE
             by (rule notE [OF z_Het z_Hm])
            next
             assume z_Heu:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
             show FALSE
             by (rule notE [OF z_Heu z_Hn])
            qed
           qed
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 658"; *} qed
lemma ob'664:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'56: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'57: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'70: "((a_ACTIONunde_cunde_a ((a_CONSTANTunde_punde_a))))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h0806c :: c)))"
fixes a_CONSTANTunde_iunde_a
assumes a_CONSTANTunde_iunde_a_in : "(a_CONSTANTunde_iunde_a \<in> (Nat))"
assumes v'98: "(((fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_qunde_a))) \<subseteq> ((a_CONSTANTunde_NUnionunde_a (([(a_CONSTANTunde_Punde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))]))))))"
assumes v'99: "((((a_CONSTANTunde_NUnionunde_a (([(a_CONSTANTunde_Punde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))])))) \<subseteq> ((a_CONSTANTunde_NUnionunde_a ((a_CONSTANTunde_Punde_a))))))"
assumes v'100: "(((fapply (((a_VARIABLEunde_nextoutunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) = (fapply ((a_VARIABLEunde_nextoutunde_a), (a_CONSTANTunde_qunde_a)))))"
shows "(((fapply (((a_VARIABLEunde_nextoutunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<subseteq> ((a_CONSTANTunde_NUnionunde_a ((a_CONSTANTunde_Punde_a))))))"(is "PROP ?ob'664")
proof -
ML_command {* writeln "*** TLAPS ENTER 664"; *}
show "PROP ?ob'664"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_0a2e13.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_0a2e13.znn.out
;; obligation #664
$hyp "v'56" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'57" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'70" (a_ACTIONunde_cunde_a a_CONSTANTunde_punde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h0806c)
$hyp "a_CONSTANTunde_iunde_a_in" (TLA.in a_CONSTANTunde_iunde_a arith.N)
$hyp "v'98" (TLA.subseteq (TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_qunde_a)
(a_CONSTANTunde_NUnionunde_a (TLA.except a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a))))
$hyp "v'99" (TLA.subseteq (a_CONSTANTunde_NUnionunde_a (TLA.except a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))
(a_CONSTANTunde_NUnionunde_a a_CONSTANTunde_Punde_a))
$hyp "v'100" (= (TLA.fapply a_VARIABLEunde_nextoutunde_hash_primea a_CONSTANTunde_qunde_a)
(TLA.fapply a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_qunde_a))
$goal (TLA.subseteq (TLA.fapply a_VARIABLEunde_nextoutunde_hash_primea a_CONSTANTunde_qunde_a)
(a_CONSTANTunde_NUnionunde_a a_CONSTANTunde_Punde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"((a_VARIABLEunde_nextoutunde_a[a_CONSTANTunde_qunde_a]) \\subseteq a_CONSTANTunde_NUnionunde_a(except(a_CONSTANTunde_Punde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))" (is "?z_hh")
 using v'98 by blast
 have z_Hi:"(a_CONSTANTunde_NUnionunde_a(except(a_CONSTANTunde_Punde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))) \\subseteq a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a))" (is "?z_hi")
 using v'99 by blast
 have z_Hj:"((a_VARIABLEunde_nextoutunde_hash_primea[a_CONSTANTunde_qunde_a])=(a_VARIABLEunde_nextoutunde_a[a_CONSTANTunde_qunde_a]))" (is "?z_hv=?z_hl")
 using v'100 by blast
 assume z_Hk:"(~(?z_hv \\subseteq a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a)))" (is "~?z_hx")
 have z_Hy_z_Hh: "bAll(?z_hl, (\<lambda>x. (x \\in a_CONSTANTunde_NUnionunde_a(except(a_CONSTANTunde_Punde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))) == ?z_hh" (is "?z_hy == _")
 by (unfold subset_def)
 have z_Hy: "?z_hy"
 by (unfold z_Hy_z_Hh, fact z_Hh)
 have z_Hbc_z_Hy: "(\\A x:((x \\in ?z_hl)=>(x \\in a_CONSTANTunde_NUnionunde_a(except(a_CONSTANTunde_Punde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))) == ?z_hy" (is "?z_hbc == _")
 by (unfold bAll_def)
 have z_Hbc: "?z_hbc" (is "\\A x : ?z_hbf(x)")
 by (unfold z_Hbc_z_Hy, fact z_Hy)
 have z_Hbg_z_Hi: "bAll(a_CONSTANTunde_NUnionunde_a(except(a_CONSTANTunde_Punde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))), (\<lambda>x. (x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a)))) == ?z_hi" (is "?z_hbg == _")
 by (unfold subset_def)
 have z_Hbg: "?z_hbg"
 by (unfold z_Hbg_z_Hi, fact z_Hi)
 have z_Hbj_z_Hbg: "(\\A x:((x \\in a_CONSTANTunde_NUnionunde_a(except(a_CONSTANTunde_Punde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a)))) == ?z_hbg" (is "?z_hbj == _")
 by (unfold bAll_def)
 have z_Hbj: "?z_hbj" (is "\\A x : ?z_hbl(x)")
 by (unfold z_Hbj_z_Hbg, fact z_Hbg)
 have z_Hbm_z_Hk: "(~bAll(?z_hv, (\<lambda>x. (x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a))))) == (~?z_hx)" (is "?z_hbm == ?z_hk")
 by (unfold subset_def)
 have z_Hbm: "?z_hbm" (is "~?z_hbn")
 by (unfold z_Hbm_z_Hk, fact z_Hk)
 have z_Hbo_z_Hbm: "(~(\\A x:((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a))))) == ?z_hbm" (is "?z_hbo == _")
 by (unfold bAll_def)
 have z_Hbo: "?z_hbo" (is "~(\\A x : ?z_hbs(x))")
 by (unfold z_Hbo_z_Hbm, fact z_Hbm)
 have z_Hbt: "(\\E x:(~((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a)))))" (is "\\E x : ?z_hbv(x)")
 by (rule zenon_notallex_0 [of "?z_hbs", OF z_Hbo])
 have z_Hbw: "?z_hbv((CHOOSE x:(~((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a))))))" (is "~(?z_hby=>?z_hbz)")
 by (rule zenon_ex_choose_0 [of "?z_hbv", OF z_Hbt])
 have z_Hby: "?z_hby"
 by (rule zenon_notimply_0 [OF z_Hbw])
 have z_Hca: "(~?z_hbz)"
 by (rule zenon_notimply_1 [OF z_Hbw])
 have z_Hcb: "?z_hbl((CHOOSE x:(~((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a))))))" (is "?z_hcc=>_")
 by (rule zenon_all_0 [of "?z_hbl" "(CHOOSE x:(~((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a)))))", OF z_Hbj])
 show FALSE
 proof (rule zenon_imply [OF z_Hcb])
  assume z_Hcd:"(~?z_hcc)"
  have z_Hce: "?z_hbf((CHOOSE x:(~((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a))))))" (is "?z_hcf=>_")
  by (rule zenon_all_0 [of "?z_hbf" "(CHOOSE x:(~((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a)))))", OF z_Hbc])
  show FALSE
  proof (rule zenon_imply [OF z_Hce])
   assume z_Hcg:"(~?z_hcf)"
   show FALSE
   proof (rule notE [OF z_Hcg])
    have z_Hcf: "?z_hcf"
    by (rule subst [where P="(\<lambda>zenon_Via. ((CHOOSE x:(~((x \\in ?z_hv)=>(x \\in a_CONSTANTunde_NUnionunde_a(a_CONSTANTunde_Punde_a))))) \\in zenon_Via))", OF z_Hj], fact z_Hby)
    thus "?z_hcf" .
   qed
  next
   assume z_Hcc:"?z_hcc"
   show FALSE
   by (rule notE [OF z_Hcd z_Hcc])
  qed
 next
  assume z_Hbz:"?z_hbz"
  show FALSE
  by (rule notE [OF z_Hca z_Hbz])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 664"; *} qed
lemma ob'753:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'56: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'57: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'70: "((a_ACTIONunde_cunde_a ((a_CONSTANTunde_punde_a))))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h0806c :: c)))"
fixes a_CONSTANTunde_iunde_a
assumes a_CONSTANTunde_iunde_a_in : "(a_CONSTANTunde_iunde_a \<in> (Nat))"
fixes a_CONSTANTunde_waunde_a
assumes a_CONSTANTunde_waunde_a_in : "(a_CONSTANTunde_waunde_a \<in> ((a_h68829a :: c)))"
(* usable definition CONSTANT_za_ suppressed *)
assumes v'104: "((((a_STATEunde_PVunde_a ((a_CONSTANTunde_zaunde_a)))) = ([ a_CONSTANTunde_junde_a \<in> (Nat)  \<mapsto> (fapply (((a_STATEunde_PVunde_a ((a_CONSTANTunde_zaunde_a)))), (a_CONSTANTunde_junde_a)))])))"
assumes v'105: "((((h6db5c ((a_CONSTANTunde_waunde_a)) :: c)) = ([ a_CONSTANTunde_junde_a \<in> (Nat)  \<mapsto> (fapply (((h6db5c ((a_CONSTANTunde_waunde_a)) :: c)), (a_CONSTANTunde_junde_a)))])))"
assumes v'106: "(((a_CONSTANTunde_waunde_a) = ([ a_CONSTANTunde_junde_a \<in> (Nat)  \<mapsto> (fapply ((a_CONSTANTunde_waunde_a), (a_CONSTANTunde_junde_a)))])))"
assumes v'107: "(((a_CONSTANTunde_zaunde_a) = ([ a_CONSTANTunde_junde_a \<in> (Nat)  \<mapsto> (fapply ((a_CONSTANTunde_zaunde_a), (a_CONSTANTunde_junde_a)))])))"
assumes v'108: "(((fapply (((a_STATEunde_PVunde_a ((a_CONSTANTunde_zaunde_a)))), (a_CONSTANTunde_iunde_a))) = (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))"
assumes v'109: "((\<And> a_CONSTANTunde_junde_a :: c. a_CONSTANTunde_junde_a \<in> (Nat) \<Longrightarrow> ((((a_CONSTANTunde_junde_a) \<noteq> (a_CONSTANTunde_iunde_a))) \<Longrightarrow> (((fapply (((a_STATEunde_PVunde_a ((a_CONSTANTunde_zaunde_a)))), (a_CONSTANTunde_junde_a))) = (fapply (((a_STATEunde_PVunde_a ((a_CONSTANTunde_waunde_a)))), (a_CONSTANTunde_junde_a))))))))"
assumes v'110: "(((fapply ((a_CONSTANTunde_waunde_a), (a_CONSTANTunde_iunde_a))) = (a_CONSTANTunde_punde_a)))"
assumes v'111: "(((a_CONSTANTunde_Punde_a) = ((h6db5c ((a_CONSTANTunde_waunde_a)) :: c))))"
assumes v'112: "((\<And> a_CONSTANTunde_junde_a :: c. a_CONSTANTunde_junde_a \<in> (Nat) \<Longrightarrow> ((((a_CONSTANTunde_junde_a) \<noteq> (a_CONSTANTunde_iunde_a))) \<Longrightarrow> (((((fapply ((a_CONSTANTunde_waunde_a), (a_CONSTANTunde_junde_a))) \<noteq> (a_CONSTANTunde_punde_a))) \<and> (((fapply (((h6db5c ((a_CONSTANTunde_waunde_a)) :: c)), (a_CONSTANTunde_junde_a))) = (fapply (((a_STATEunde_PVunde_a ((a_CONSTANTunde_waunde_a)))), (a_CONSTANTunde_junde_a))))))))))"
assumes v'113: "(((a_CONSTANTunde_NotAProcunde_a) \<notin> (a_CONSTANTunde_Procunde_a)))"
shows "((([(a_CONSTANTunde_Punde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))]) = ((a_STATEunde_PVunde_a ((a_CONSTANTunde_zaunde_a))))))"(is "PROP ?ob'753")
proof -
ML_command {* writeln "*** TLAPS ENTER 753"; *}
show "PROP ?ob'753"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_37168f.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_37168f.znn.out
;; obligation #753
$hyp "v'56" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'57" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'70" (a_ACTIONunde_cunde_a a_CONSTANTunde_punde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h0806c)
$hyp "a_CONSTANTunde_iunde_a_in" (TLA.in a_CONSTANTunde_iunde_a arith.N)
$hyp "a_CONSTANTunde_waunde_a_in" (TLA.in a_CONSTANTunde_waunde_a a_h68829a)
$hyp "v'104" (= (a_STATEunde_PVunde_a a_CONSTANTunde_zaunde_a)
(TLA.Fcn arith.N ((a_CONSTANTunde_junde_a) (TLA.fapply (a_STATEunde_PVunde_a a_CONSTANTunde_zaunde_a) a_CONSTANTunde_junde_a))))
$hyp "v'105" (= (h6db5c a_CONSTANTunde_waunde_a)
(TLA.Fcn arith.N ((a_CONSTANTunde_junde_a) (TLA.fapply (h6db5c a_CONSTANTunde_waunde_a) a_CONSTANTunde_junde_a))))
$hyp "v'106" (= a_CONSTANTunde_waunde_a
(TLA.Fcn arith.N ((a_CONSTANTunde_junde_a) (TLA.fapply a_CONSTANTunde_waunde_a a_CONSTANTunde_junde_a))))
$hyp "v'107" (= a_CONSTANTunde_zaunde_a
(TLA.Fcn arith.N ((a_CONSTANTunde_junde_a) (TLA.fapply a_CONSTANTunde_zaunde_a a_CONSTANTunde_junde_a))))
$hyp "v'108" (= (TLA.fapply (a_STATEunde_PVunde_a a_CONSTANTunde_zaunde_a) a_CONSTANTunde_iunde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a))
$hyp "v'109" (TLA.bAll arith.N ((a_CONSTANTunde_junde_a) (=> (-. (= a_CONSTANTunde_junde_a
a_CONSTANTunde_iunde_a)) (= (TLA.fapply (a_STATEunde_PVunde_a a_CONSTANTunde_zaunde_a) a_CONSTANTunde_junde_a)
(TLA.fapply (a_STATEunde_PVunde_a a_CONSTANTunde_waunde_a) a_CONSTANTunde_junde_a)))))
$hyp "v'110" (= (TLA.fapply a_CONSTANTunde_waunde_a a_CONSTANTunde_iunde_a)
a_CONSTANTunde_punde_a)
$hyp "v'111" (= a_CONSTANTunde_Punde_a
(h6db5c a_CONSTANTunde_waunde_a))
$hyp "v'112" (TLA.bAll arith.N ((a_CONSTANTunde_junde_a) (=> (-. (= a_CONSTANTunde_junde_a
a_CONSTANTunde_iunde_a)) (/\ (-. (= (TLA.fapply a_CONSTANTunde_waunde_a a_CONSTANTunde_junde_a)
a_CONSTANTunde_punde_a))
(= (TLA.fapply (h6db5c a_CONSTANTunde_waunde_a) a_CONSTANTunde_junde_a)
(TLA.fapply (a_STATEunde_PVunde_a a_CONSTANTunde_waunde_a) a_CONSTANTunde_junde_a))))))
$hyp "v'113" (-. (TLA.in a_CONSTANTunde_NotAProcunde_a
a_CONSTANTunde_Procunde_a))
$goal (= (TLA.except a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a))
(a_STATEunde_PVunde_a a_CONSTANTunde_zaunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hp:"(a_CONSTANTunde_Punde_a=h6db5c(a_CONSTANTunde_waunde_a))" (is "_=?z_hu")
 using v'111 by blast
 have z_Hn:"bAll(Nat, (\<lambda>a_CONSTANTunde_junde_a. ((a_CONSTANTunde_junde_a~=a_CONSTANTunde_iunde_a)=>((a_STATEunde_PVunde_a(a_CONSTANTunde_zaunde_a)[a_CONSTANTunde_junde_a])=(a_STATEunde_PVunde_a(a_CONSTANTunde_waunde_a)[a_CONSTANTunde_junde_a])))))" (is "?z_hn")
 using v'109 by blast
 have z_Hi:"(a_STATEunde_PVunde_a(a_CONSTANTunde_zaunde_a)=Fcn(Nat, (\<lambda>a_CONSTANTunde_junde_a. (a_STATEunde_PVunde_a(a_CONSTANTunde_zaunde_a)[a_CONSTANTunde_junde_a]))))" (is "?z_hbe=?z_hbi")
 using v'104 by blast
 have z_Hj:"(?z_hu=Fcn(Nat, (\<lambda>a_CONSTANTunde_junde_a. (?z_hu[a_CONSTANTunde_junde_a]))))" (is "_=?z_hbk")
 using v'105 by blast
 have z_Hm:"((?z_hbe[a_CONSTANTunde_iunde_a])=(a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))" (is "?z_hbn=?z_hbo")
 using v'108 by blast
 have z_Hq:"bAll(Nat, (\<lambda>a_CONSTANTunde_junde_a. ((a_CONSTANTunde_junde_a~=a_CONSTANTunde_iunde_a)=>(((a_CONSTANTunde_waunde_a[a_CONSTANTunde_junde_a])~=a_CONSTANTunde_punde_a)&((?z_hu[a_CONSTANTunde_junde_a])=(a_STATEunde_PVunde_a(a_CONSTANTunde_waunde_a)[a_CONSTANTunde_junde_a]))))))" (is "?z_hq")
 using v'112 by blast
 assume z_Hs:"(except(a_CONSTANTunde_Punde_a, a_CONSTANTunde_iunde_a, ?z_hbo)~=?z_hbe)" (is "?z_hbx~=_")
 have z_Hby_z_Hn: "(\\A x:((x \\in Nat)=>((x~=a_CONSTANTunde_iunde_a)=>((?z_hbe[x])=(a_STATEunde_PVunde_a(a_CONSTANTunde_waunde_a)[x]))))) == ?z_hn" (is "?z_hby == _")
 by (unfold bAll_def)
 have z_Hby: "?z_hby" (is "\\A x : ?z_hch(x)")
 by (unfold z_Hby_z_Hn, fact z_Hn)
 have z_Hci_z_Hq: "(\\A x:((x \\in Nat)=>((x~=a_CONSTANTunde_iunde_a)=>(((a_CONSTANTunde_waunde_a[x])~=a_CONSTANTunde_punde_a)&((?z_hu[x])=(a_STATEunde_PVunde_a(a_CONSTANTunde_waunde_a)[x])))))) == ?z_hq" (is "?z_hci == _")
 by (unfold bAll_def)
 have z_Hci: "?z_hci" (is "\\A x : ?z_hcq(x)")
 by (unfold z_Hci_z_Hq, fact z_Hq)
 have z_Hcr: "(~(((isAFcn(?z_hbx)&isAFcn(?z_hbe))&(DOMAIN(?z_hbx)=DOMAIN(?z_hbe)))&(\\A zenon_Vg:((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))))" (is "~(?z_hct&?z_hda)")
 by (rule zenon_notfunequal_0 [of "?z_hbx" "?z_hbe", OF z_Hs])
 show FALSE
 proof (rule zenon_notand [OF z_Hcr])
  assume z_Hdh:"(~?z_hct)" (is "~(?z_hcu&?z_hcx)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdh])
   assume z_Hdi:"(~?z_hcu)" (is "~(?z_hcv&?z_hcw)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdi])
    assume z_Hdj:"(~?z_hcv)"
    show FALSE
    by (rule zenon_notisafcn_except [of "a_CONSTANTunde_Punde_a" "a_CONSTANTunde_iunde_a" "?z_hbo", OF z_Hdj])
   next
    assume z_Hdk:"(~?z_hcw)"
    have z_Hdl: "(~isAFcn(?z_hbi))" (is "~?z_hdm")
    by (rule subst [where P="(\<lambda>zenon_Vwka. (~isAFcn(zenon_Vwka)))", OF z_Hi z_Hdk])
    show FALSE
    by (rule zenon_notisafcn_fcn [of "Nat" "(\<lambda>a_CONSTANTunde_junde_a. (?z_hbe[a_CONSTANTunde_junde_a]))", OF z_Hdl])
   qed
  next
   assume z_Hdr:"(DOMAIN(?z_hbx)~=DOMAIN(?z_hbe))" (is "?z_hcy~=?z_hcz")
   have z_Hds: "(DOMAIN(a_CONSTANTunde_Punde_a)~=?z_hcz)" (is "?z_hdt~=_")
   by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vbla. (zenon_Vbla~=?z_hcz))" "a_CONSTANTunde_Punde_a" "a_CONSTANTunde_iunde_a" "?z_hbo", OF z_Hdr])
   have z_Hdx: "(DOMAIN(?z_hu)~=?z_hcz)" (is "?z_hdy~=_")
   by (rule subst [where P="(\<lambda>zenon_Vela. (DOMAIN(zenon_Vela)~=?z_hcz))", OF z_Hp z_Hds])
   have z_Hed: "(DOMAIN(?z_hbk)~=?z_hcz)" (is "?z_hee~=_")
   by (rule subst [where P="(\<lambda>zenon_Vela. (DOMAIN(zenon_Vela)~=?z_hcz))", OF z_Hj z_Hdx])
   have z_Hef: "(Nat~=?z_hcz)"
   by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vbla. (zenon_Vbla~=?z_hcz))" "Nat" "(\<lambda>a_CONSTANTunde_junde_a. (?z_hu[a_CONSTANTunde_junde_a]))", OF z_Hed])
   have z_Heg: "(Nat~=DOMAIN(?z_hbi))" (is "_~=?z_heh")
   by (rule subst [where P="(\<lambda>zenon_Vqla. (Nat~=DOMAIN(zenon_Vqla)))", OF z_Hi z_Hef])
   have z_Hem: "(Nat~=Nat)"
   by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vpla. (Nat~=zenon_Vpla))" "Nat" "(\<lambda>a_CONSTANTunde_junde_a. (?z_hbe[a_CONSTANTunde_junde_a]))", OF z_Heg])
   show FALSE
   by (rule zenon_noteq [OF z_Hem])
  qed
 next
  assume z_Heq:"(~?z_hda)" (is "~(\\A x : ?z_her(x))")
  have z_Hes: "(\\E zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg])))))" (is "\\E x : ?z_heu(x)")
  by (rule zenon_notallex_0 [of "?z_her", OF z_Heq])
  have z_Hev: "?z_heu((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))))" (is "~(?z_hex=>?z_hey)")
  by (rule zenon_ex_choose_0 [of "?z_heu", OF z_Hes])
  have z_Hex: "?z_hex"
  by (rule zenon_notimply_0 [OF z_Hev])
  have z_Hez: "((?z_hbx[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg])))))])~=(?z_hbe[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg])))))]))" (is "?z_hfa~=?z_hfb")
  by (rule zenon_notimply_1 [OF z_Hev])
  have z_Hfc: "((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(?z_hbi))" (is "?z_hfc")
  by (rule subst [where P="(\<lambda>zenon_Vfc. ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(zenon_Vfc)))", OF z_Hi z_Hex])
  have z_Hfh: "((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in Nat)" (is "?z_hfh")
  by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vec. ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in zenon_Vec))" "Nat" "(\<lambda>a_CONSTANTunde_junde_a. (?z_hbe[a_CONSTANTunde_junde_a]))", OF z_Hfc])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vcc. (zenon_Vcc~=?z_hfb))" "a_CONSTANTunde_Punde_a" "a_CONSTANTunde_iunde_a" "?z_hbo" "(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg])))))", OF z_Hez])
   assume z_Hfo:"((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(a_CONSTANTunde_Punde_a))" (is "?z_hfo")
   assume z_Hfp:"(a_CONSTANTunde_iunde_a=(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))))" (is "_=?z_hew")
   assume z_Hfq:"(?z_hbo~=?z_hfb)"
   show FALSE
   proof (rule zenon_em [of "(?z_hfb=?z_hfb)"])
    assume z_Hfr:"(?z_hfb=?z_hfb)"
    show FALSE
    proof (rule notE [OF z_Hez])
     have z_Hfs: "(?z_hfb=?z_hfa)"
     proof (rule zenon_nnpp [of "(?z_hfb=?z_hfa)"])
      assume z_Hft:"(?z_hfb~=?z_hfa)"
      show FALSE
      proof (rule notE [OF z_Hft])
       have z_Hfu: "(?z_hbn=?z_hfb)"
       proof (rule zenon_nnpp [of "(?z_hbn=?z_hfb)"])
        assume z_Hfv:"(?z_hbn~=?z_hfb)"
        show FALSE
        proof (rule zenon_em [of "(?z_hfb=?z_hfb)"])
         assume z_Hfr:"(?z_hfb=?z_hfb)"
         show FALSE
         proof (rule notE [OF z_Hfv])
          have z_Hfw: "(?z_hfb=?z_hbn)"
          proof (rule zenon_nnpp [of "(?z_hfb=?z_hbn)"])
           assume z_Hfx:"(?z_hfb~=?z_hbn)"
           show FALSE
           proof (rule zenon_noteq [of "?z_hbn"])
            have z_Hfy: "(?z_hew=a_CONSTANTunde_iunde_a)"
            by (rule sym [OF z_Hfp])
            have z_Hfz: "(?z_hbn~=?z_hbn)"
            by (rule subst [where P="(\<lambda>zenon_Vama. ((?z_hbe[zenon_Vama])~=?z_hbn))", OF z_Hfy], fact z_Hfx)
            thus "(?z_hbn~=?z_hbn)" .
           qed
          qed
          have z_Hfu: "(?z_hbn=?z_hfb)"
          by (rule subst [where P="(\<lambda>zenon_Vbma. (zenon_Vbma=?z_hfb))", OF z_Hfw], fact z_Hfr)
          thus "(?z_hbn=?z_hfb)" .
         qed
        next
         assume z_Hgh:"(?z_hfb~=?z_hfb)"
         show FALSE
         by (rule zenon_noteq [OF z_Hgh])
        qed
       qed
       have z_Hgi: "(?z_hbo=?z_hfa)"
       proof (rule zenon_nnpp [of "(?z_hbo=?z_hfa)"])
        assume z_Hgj:"(?z_hbo~=?z_hfa)"
        show FALSE
        proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vhb. (?z_hbo~=zenon_Vhb))" "a_CONSTANTunde_Punde_a" "a_CONSTANTunde_iunde_a" "?z_hbo" "?z_hew", OF z_Hgj])
         assume z_Hfo:"?z_hfo"
         assume z_Hfp:"(a_CONSTANTunde_iunde_a=?z_hew)"
         assume z_Hgn:"(?z_hbo~=?z_hbo)"
         show FALSE
         by (rule zenon_noteq [OF z_Hgn])
        next
         assume z_Hfo:"?z_hfo"
         assume z_Hgo:"(a_CONSTANTunde_iunde_a~=?z_hew)"
         assume z_Hgp:"(?z_hbo~=(a_CONSTANTunde_Punde_a[?z_hew]))" (is "_~=?z_hgq")
         show FALSE
         by (rule notE [OF z_Hgo z_Hfp])
        next
         assume z_Hgr:"(~?z_hfo)"
         show FALSE
         by (rule notE [OF z_Hgr z_Hfo])
        qed
       qed
       have z_Hgs: "(?z_hfb=?z_hbo)"
       by (rule subst [where P="(\<lambda>zenon_Vcma. (zenon_Vcma=?z_hbo))", OF z_Hfu], fact z_Hm)
       have z_Hfs: "(?z_hfb=?z_hfa)"
       by (rule subst [where P="(\<lambda>zenon_Vdma. (?z_hfb=zenon_Vdma))", OF z_Hgi], fact z_Hgs)
       thus "(?z_hfb=?z_hfa)" .
      qed
     qed
     have z_Hey: "?z_hey"
     by (rule subst [where P="(\<lambda>zenon_Vbma. (zenon_Vbma=?z_hfb))", OF z_Hfs], fact z_Hfr)
     thus "?z_hey" .
    qed
   next
    assume z_Hgh:"(?z_hfb~=?z_hfb)"
    show FALSE
    by (rule zenon_noteq [OF z_Hgh])
   qed
  next
   assume z_Hfo:"((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(a_CONSTANTunde_Punde_a))" (is "?z_hfo")
   assume z_Hgo:"(a_CONSTANTunde_iunde_a~=(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))))" (is "_~=?z_hew")
   assume z_Hgz:"((a_CONSTANTunde_Punde_a[?z_hew])~=?z_hfb)" (is "?z_hgq~=_")
   have z_Hha: "((?z_hu[?z_hew])~=?z_hfb)" (is "?z_hhb~=_")
   by (rule subst [where P="(\<lambda>zenon_Vxla. ((zenon_Vxla[?z_hew])~=?z_hfb))", OF z_Hp z_Hgz])
   have z_Hhg: "?z_hch(?z_hew)" (is "_=>?z_hhh")
   by (rule zenon_all_0 [of "?z_hch" "?z_hew", OF z_Hby])
   show FALSE
   proof (rule zenon_imply [OF z_Hhg])
    assume z_Hhi:"(~?z_hfh)"
    show FALSE
    by (rule notE [OF z_Hhi z_Hfh])
   next
    assume z_Hhh:"?z_hhh" (is "?z_hhj=>?z_hhk")
    show FALSE
    proof (rule zenon_imply [OF z_Hhh])
     assume z_Hhl:"(~?z_hhj)" (is "~~?z_hfy")
     have z_Hfy: "?z_hfy"
     by (rule zenon_notnot_0 [OF z_Hhl])
     show FALSE
     by (rule zenon_eqsym [OF z_Hfy z_Hgo])
    next
     assume z_Hhk:"?z_hhk" (is "_=?z_hhm")
     have z_Hhn: "?z_hcq(?z_hew)" (is "_=>?z_hho")
     by (rule zenon_all_0 [of "?z_hcq" "?z_hew", OF z_Hci])
     show FALSE
     proof (rule zenon_imply [OF z_Hhn])
      assume z_Hhi:"(~?z_hfh)"
      show FALSE
      by (rule notE [OF z_Hhi z_Hfh])
     next
      assume z_Hho:"?z_hho" (is "_=>?z_hhp")
      show FALSE
      proof (rule zenon_imply [OF z_Hho])
       assume z_Hhl:"(~?z_hhj)" (is "~~?z_hfy")
       have z_Hfy: "?z_hfy"
       by (rule zenon_notnot_0 [OF z_Hhl])
       show FALSE
       by (rule zenon_eqsym [OF z_Hfy z_Hgo])
      next
       assume z_Hhp:"?z_hhp" (is "?z_hhq&?z_hhr")
       have z_Hhr: "?z_hhr"
       by (rule zenon_and_1 [OF z_Hhp])
       show FALSE
       proof (rule zenon_em [of "(?z_hfb=?z_hfb)"])
        assume z_Hfr:"(?z_hfb=?z_hfb)"
        show FALSE
        proof (rule notE [OF z_Hha])
         have z_Hhs: "(?z_hfb=?z_hhb)"
         proof (rule zenon_nnpp [of "(?z_hfb=?z_hhb)"])
          assume z_Hht:"(?z_hfb~=?z_hhb)"
          show FALSE
          proof (rule notE [OF z_Hht])
           have z_Hhu: "(?z_hhm=?z_hhb)"
           by (rule sym [OF z_Hhr])
           have z_Hhs: "(?z_hfb=?z_hhb)"
           by (rule subst [where P="(\<lambda>zenon_Vdma. (?z_hfb=zenon_Vdma))", OF z_Hhu], fact z_Hhk)
           thus "(?z_hfb=?z_hhb)" .
          qed
         qed
         have z_Hhv: "(?z_hhb=?z_hfb)"
         by (rule subst [where P="(\<lambda>zenon_Vbma. (zenon_Vbma=?z_hfb))", OF z_Hhs], fact z_Hfr)
         thus "(?z_hhb=?z_hfb)" .
        qed
       next
        assume z_Hgh:"(?z_hfb~=?z_hfb)"
        show FALSE
        by (rule zenon_noteq [OF z_Hgh])
       qed
      qed
     qed
    qed
   qed
  next
   assume z_Hgr:"(~((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(a_CONSTANTunde_Punde_a)))" (is "~?z_hfo")
   have z_Hhw: "(~((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(?z_hu)))" (is "~?z_hhx")
   by (rule subst [where P="(\<lambda>zenon_Vmc. (~((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(zenon_Vmc))))", OF z_Hp z_Hgr])
   have z_Hid: "(~((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(?z_hbk)))" (is "~?z_hie")
   by (rule subst [where P="(\<lambda>zenon_Vmc. (~((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in DOMAIN(zenon_Vmc))))", OF z_Hj z_Hhw])
   have z_Hhi: "(~?z_hfh)"
   by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vlc. (~((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbe))=>((?z_hbx[zenon_Vg])=(?z_hbe[zenon_Vg]))))) \\in zenon_Vlc)))" "Nat" "(\<lambda>a_CONSTANTunde_junde_a. (?z_hu[a_CONSTANTunde_junde_a]))", OF z_Hid])
   show FALSE
   by (rule notE [OF z_Hhi z_Hfh])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 753"; *} qed
lemma ob'787:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'54: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'55: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'68: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'69: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'70: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'71: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'72: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'73: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'74: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'75: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'76: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'77: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'78: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h0806c :: c)))"
assumes v'93: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
assumes v'94: "(((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a))))))))))))"
shows "((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c''))) & ((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({}))) & (((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))) & (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) & ((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a))) & ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a))) & ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'787")
proof -
ML_command {* writeln "*** TLAPS ENTER 787"; *}
show "PROP ?ob'787"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_4ffce7.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_4ffce7.znn.out
;; obligation #787
$hyp "v'54" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'55" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'68" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'69" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'70" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'71" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'72" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'73" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'74" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'75" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'76" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'77" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'78" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h0806c)
$hyp "v'93" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$hyp "v'94" (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a))))))
$goal (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "c")
(= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
(= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a))))))
(= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))
(/\ (= a_VARIABLEunde_resultunde_hash_primea a_VARIABLEunde_resultunde_a)
(= a_VARIABLEunde_A2unde_hash_primea a_VARIABLEunde_A2unde_a)
(= a_VARIABLEunde_A3unde_hash_primea a_VARIABLEunde_A3unde_a)
(= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_nbpartunde_hash_primea a_VARIABLEunde_nbpartunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''c'')" (is "?z_ht=?z_hw")
 using v'69 by blast
 have z_Hf:"(a_VARIABLEunde_lnbpartunde_hash_primea=except(a_VARIABLEunde_lnbpartunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])))" (is "_=?z_hy")
 using v'70 by blast
 have z_Hg:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hbd")
 using v'71 by blast
 have z_Hh:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, ((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]) +  -.(1))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hbp")
 using v'72 by blast
 have z_Hr:"((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))))" (is "?z_hba=?z_hca")
 using v'94 by blast
 have z_Hq:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})" (is "?z_hcg=_")
 using v'93 by blast
 have z_Hd:"cond((?z_hcg~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)), (cond((?z_hba=?z_hca), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))))" (is "?z_hd")
 using v'68 by blast
 have z_Hi:"(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)"
 using v'73 by blast
 have z_Hj:"(a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)"
 using v'74 by blast
 have z_Hk:"(a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)"
 using v'75 by blast
 have z_Hl:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'76 by blast
 have z_Hm:"(a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)"
 using v'77 by blast
 have z_Hn:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'78 by blast
 assume z_Hs:"(~((?z_ht=?z_hw)&((a_VARIABLEunde_lnbpartunde_hash_primea=?z_hy)&((a_VARIABLEunde_knownunde_hash_primea=?z_hbd)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbp)&((?z_hcg={})&((?z_hba=?z_hca)&((a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))&((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)&((a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)&((a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)&((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&((a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)))))))))))))))" (is "~(?z_he&?z_hdk)")
 show FALSE
 proof (rule zenon_notand [OF z_Hs])
  assume z_Hdw:"(?z_ht~=?z_hw)"
  show FALSE
  by (rule notE [OF z_Hdw z_He])
 next
  assume z_Hdx:"(~?z_hdk)" (is "~(?z_hf&?z_hdl)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdx])
   assume z_Hdy:"(a_VARIABLEunde_lnbpartunde_hash_primea~=?z_hy)"
   show FALSE
   by (rule notE [OF z_Hdy z_Hf])
  next
   assume z_Hdz:"(~?z_hdl)" (is "~(?z_hg&?z_hdm)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdz])
    assume z_Hea:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbd)"
    show FALSE
    by (rule notE [OF z_Hea z_Hg])
   next
    assume z_Heb:"(~?z_hdm)" (is "~(?z_hh&?z_hdn)")
    show FALSE
    proof (rule zenon_notand [OF z_Heb])
     assume z_Hec:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbp)"
     show FALSE
     by (rule notE [OF z_Hec z_Hh])
    next
     assume z_Hed:"(~?z_hdn)" (is "~(?z_hq&?z_hdo)")
     show FALSE
     proof (rule zenon_notand [OF z_Hed])
      assume z_Hci:"(?z_hcg~={})"
      show FALSE
      by (rule notE [OF z_Hci z_Hq])
     next
      assume z_Hee:"(~?z_hdo)" (is "~(?z_hr&?z_hdp)")
      show FALSE
      proof (rule zenon_notand [OF z_Hee])
       assume z_Hef:"(?z_hba~=?z_hca)"
       show FALSE
       by (rule notE [OF z_Hef z_Hr])
      next
       assume z_Heg:"(~?z_hdp)" (is "~(?z_hct&?z_hdq)")
       show FALSE
       proof (rule zenon_notand [OF z_Heg])
        assume z_Heh:"(a_VARIABLEunde_nextoutunde_hash_primea~=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hcu")
        show FALSE
        proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hcg~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" "(cond(?z_hr, ?z_hct, (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
         assume z_Hci:"(?z_hcg~={})"
         assume z_Hcj:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "?z_hck&?z_hco")
         show FALSE
         by (rule notE [OF z_Hci z_Hq])
        next
         assume z_Hek:"(~(?z_hcg~={}))"
         assume z_Hcr:"(cond(?z_hr, ?z_hct, (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hcs&?z_hcx")
         have z_Hcs: "?z_hcs"
         by (rule zenon_and_0 [OF z_Hcr])
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hr" "?z_hct" "(TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))", OF z_Hcs])
          assume z_Hr:"?z_hr"
          assume z_Hct:"?z_hct"
          show FALSE
          by (rule notE [OF z_Heh z_Hct])
         next
          assume z_Hef:"(?z_hba~=?z_hca)"
          assume z_Hcv:"(TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "?z_hcw&?z_hco")
          show FALSE
          by (rule notE [OF z_Hef z_Hr])
         qed
        qed
       next
        assume z_Hel:"(~?z_hdq)" (is "~(?z_hcx&?z_hdr)")
        show FALSE
        proof (rule zenon_notand [OF z_Hel])
         assume z_Hem:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))" (is "_~=?z_hcy")
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hcg~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" "(cond(?z_hr, ?z_hct, (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&?z_hcx)", OF z_Hd])
          assume z_Hci:"(?z_hcg~={})"
          assume z_Hcj:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "?z_hck&?z_hco")
          show FALSE
          by (rule notE [OF z_Hci z_Hq])
         next
          assume z_Hek:"(~(?z_hcg~={}))"
          assume z_Hcr:"(cond(?z_hr, ?z_hct, (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&?z_hcx)" (is "?z_hcs&_")
          have z_Hcx: "?z_hcx"
          by (rule zenon_and_1 [OF z_Hcr])
          show FALSE
          by (rule notE [OF z_Hem z_Hcx])
         qed
        next
         assume z_Hen:"(~?z_hdr)" (is "~(?z_hi&?z_hds)")
         show FALSE
         proof (rule zenon_notand [OF z_Hen])
          assume z_Heo:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
          show FALSE
          by (rule notE [OF z_Heo z_Hi])
         next
          assume z_Hep:"(~?z_hds)" (is "~(?z_hj&?z_hdt)")
          show FALSE
          proof (rule zenon_notand [OF z_Hep])
           assume z_Heq:"(a_VARIABLEunde_A2unde_hash_primea~=a_VARIABLEunde_A2unde_a)"
           show FALSE
           by (rule notE [OF z_Heq z_Hj])
          next
           assume z_Her:"(~?z_hdt)" (is "~(?z_hk&?z_hdu)")
           show FALSE
           proof (rule zenon_notand [OF z_Her])
            assume z_Hes:"(a_VARIABLEunde_A3unde_hash_primea~=a_VARIABLEunde_A3unde_a)"
            show FALSE
            by (rule notE [OF z_Hes z_Hk])
           next
            assume z_Het:"(~?z_hdu)" (is "~(?z_hl&?z_hdv)")
            show FALSE
            proof (rule zenon_notand [OF z_Het])
             assume z_Heu:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
             show FALSE
             by (rule notE [OF z_Heu z_Hl])
            next
             assume z_Hev:"(~?z_hdv)" (is "~(?z_hm&?z_hn)")
             show FALSE
             proof (rule zenon_notand [OF z_Hev])
              assume z_Hew:"(a_VARIABLEunde_nbpartunde_hash_primea~=a_VARIABLEunde_nbpartunde_a)"
              show FALSE
              by (rule notE [OF z_Hew z_Hm])
             next
              assume z_Hex:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
              show FALSE
              by (rule notE [OF z_Hex z_Hn])
             qed
            qed
           qed
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 787"; *} qed
lemma ob'986:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'54: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'55: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'68: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'69: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'70: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'71: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'72: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'73: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'74: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'75: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'76: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'77: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'78: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h0806c :: c)))"
assumes v'94: "(((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a))))))))))))"
assumes v'95: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
shows "((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c''))) & ((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({}))) & (((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))) & (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) & ((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a))) & ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a))) & ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'986")
proof -
ML_command {* writeln "*** TLAPS ENTER 986"; *}
show "PROP ?ob'986"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_b63013.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_b63013.znn.out
;; obligation #986
$hyp "v'54" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'55" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'68" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'69" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'70" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'71" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'72" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'73" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'74" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'75" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'76" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'77" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'78" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h0806c)
$hyp "v'94" (-. (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'95" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$goal (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "c")
(= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
(-. (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))
(/\ (= a_VARIABLEunde_resultunde_hash_primea a_VARIABLEunde_resultunde_a)
(= a_VARIABLEunde_A2unde_hash_primea a_VARIABLEunde_A2unde_a)
(= a_VARIABLEunde_A3unde_hash_primea a_VARIABLEunde_A3unde_a)
(= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_nbpartunde_hash_primea a_VARIABLEunde_nbpartunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''c'')" (is "?z_ht=?z_hw")
 using v'69 by blast
 have z_Hf:"(a_VARIABLEunde_lnbpartunde_hash_primea=except(a_VARIABLEunde_lnbpartunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])))" (is "_=?z_hy")
 using v'70 by blast
 have z_Hg:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hbd")
 using v'71 by blast
 have z_Hh:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, ((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]) +  -.(1))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hbp")
 using v'72 by blast
 have z_Hq:"((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])~=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))))" (is "?z_hba~=?z_hca")
 using v'94 by blast
 have z_Hr:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})" (is "?z_hcg=_")
 using v'95 by blast
 have z_Hd:"cond((?z_hcg~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)), (cond((?z_hba=?z_hca), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))))" (is "?z_hd")
 using v'68 by blast
 have z_Hi:"(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)"
 using v'73 by blast
 have z_Hj:"(a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)"
 using v'74 by blast
 have z_Hk:"(a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)"
 using v'75 by blast
 have z_Hl:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'76 by blast
 have z_Hm:"(a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)"
 using v'77 by blast
 have z_Hn:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'78 by blast
 assume z_Hs:"(~((?z_ht=?z_hw)&((a_VARIABLEunde_lnbpartunde_hash_primea=?z_hy)&((a_VARIABLEunde_knownunde_hash_primea=?z_hbd)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbp)&((?z_hcg={})&((?z_hba~=?z_hca)&((a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))&((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)&((a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)&((a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)&((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&((a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)))))))))))))))" (is "~(?z_he&?z_hdl)")
 show FALSE
 proof (rule zenon_notand [OF z_Hs])
  assume z_Hdx:"(?z_ht~=?z_hw)"
  show FALSE
  by (rule notE [OF z_Hdx z_He])
 next
  assume z_Hdy:"(~?z_hdl)" (is "~(?z_hf&?z_hdm)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdy])
   assume z_Hdz:"(a_VARIABLEunde_lnbpartunde_hash_primea~=?z_hy)"
   show FALSE
   by (rule notE [OF z_Hdz z_Hf])
  next
   assume z_Hea:"(~?z_hdm)" (is "~(?z_hg&?z_hdn)")
   show FALSE
   proof (rule zenon_notand [OF z_Hea])
    assume z_Heb:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbd)"
    show FALSE
    by (rule notE [OF z_Heb z_Hg])
   next
    assume z_Hec:"(~?z_hdn)" (is "~(?z_hh&?z_hdo)")
    show FALSE
    proof (rule zenon_notand [OF z_Hec])
     assume z_Hed:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbp)"
     show FALSE
     by (rule notE [OF z_Hed z_Hh])
    next
     assume z_Hee:"(~?z_hdo)" (is "~(?z_hr&?z_hdp)")
     show FALSE
     proof (rule zenon_notand [OF z_Hee])
      assume z_Hci:"(?z_hcg~={})"
      show FALSE
      by (rule notE [OF z_Hci z_Hr])
     next
      assume z_Hef:"(~?z_hdp)" (is "~(?z_hq&?z_hdq)")
      show FALSE
      proof (rule zenon_notand [OF z_Hef])
       assume z_Heg:"(~?z_hq)" (is "~~?z_hct")
       show FALSE
       by (rule notE [OF z_Heg z_Hq])
      next
       assume z_Heh:"(~?z_hdq)" (is "~(?z_hco&?z_hdr)")
       show FALSE
       proof (rule zenon_notand [OF z_Heh])
        assume z_Hei:"(a_VARIABLEunde_nextoutunde_hash_primea~=a_VARIABLEunde_nextoutunde_a)"
        show FALSE
        proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hcg~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hco)" "(cond((?z_hba=?z_hca), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hco))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
         assume z_Hci:"(?z_hcg~={})"
         assume z_Hcj:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hco)" (is "?z_hck&_")
         show FALSE
         by (rule notE [OF z_Hci z_Hr])
        next
         assume z_Hel:"(~(?z_hcg~={}))"
         assume z_Hcr:"(cond((?z_hba=?z_hca), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hco))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hcs&?z_hcy")
         have z_Hcs: "?z_hcs"
         by (rule zenon_and_0 [OF z_Hcr])
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hba=?z_hca)" "(a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" "(TRUE&?z_hco)", OF z_Hcs])
          assume z_Hct:"(?z_hba=?z_hca)"
          assume z_Hcu:"(a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_=?z_hcv")
          show FALSE
          by (rule notE [OF z_Hq z_Hct])
         next
          assume z_Hq:"?z_hq"
          assume z_Hcw:"(TRUE&?z_hco)" (is "?z_hcx&_")
          have z_Hco: "?z_hco"
          by (rule zenon_and_1 [OF z_Hcw])
          show FALSE
          by (rule notE [OF z_Hei z_Hco])
         qed
        qed
       next
        assume z_Hem:"(~?z_hdr)" (is "~(?z_hcy&?z_hds)")
        show FALSE
        proof (rule zenon_notand [OF z_Hem])
         assume z_Hen:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))" (is "_~=?z_hcz")
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hcg~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hco)" "(cond((?z_hba=?z_hca), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hco))&?z_hcy)", OF z_Hd])
          assume z_Hci:"(?z_hcg~={})"
          assume z_Hcj:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hco)" (is "?z_hck&_")
          show FALSE
          by (rule notE [OF z_Hci z_Hr])
         next
          assume z_Hel:"(~(?z_hcg~={}))"
          assume z_Hcr:"(cond((?z_hba=?z_hca), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hco))&?z_hcy)" (is "?z_hcs&_")
          have z_Hcy: "?z_hcy"
          by (rule zenon_and_1 [OF z_Hcr])
          show FALSE
          by (rule notE [OF z_Hen z_Hcy])
         qed
        next
         assume z_Heo:"(~?z_hds)" (is "~(?z_hi&?z_hdt)")
         show FALSE
         proof (rule zenon_notand [OF z_Heo])
          assume z_Hep:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
          show FALSE
          by (rule notE [OF z_Hep z_Hi])
         next
          assume z_Heq:"(~?z_hdt)" (is "~(?z_hj&?z_hdu)")
          show FALSE
          proof (rule zenon_notand [OF z_Heq])
           assume z_Her:"(a_VARIABLEunde_A2unde_hash_primea~=a_VARIABLEunde_A2unde_a)"
           show FALSE
           by (rule notE [OF z_Her z_Hj])
          next
           assume z_Hes:"(~?z_hdu)" (is "~(?z_hk&?z_hdv)")
           show FALSE
           proof (rule zenon_notand [OF z_Hes])
            assume z_Het:"(a_VARIABLEunde_A3unde_hash_primea~=a_VARIABLEunde_A3unde_a)"
            show FALSE
            by (rule notE [OF z_Het z_Hk])
           next
            assume z_Heu:"(~?z_hdv)" (is "~(?z_hl&?z_hdw)")
            show FALSE
            proof (rule zenon_notand [OF z_Heu])
             assume z_Hev:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
             show FALSE
             by (rule notE [OF z_Hev z_Hl])
            next
             assume z_Hew:"(~?z_hdw)" (is "~(?z_hm&?z_hn)")
             show FALSE
             proof (rule zenon_notand [OF z_Hew])
              assume z_Hex:"(a_VARIABLEunde_nbpartunde_hash_primea~=a_VARIABLEunde_nbpartunde_a)"
              show FALSE
              by (rule notE [OF z_Hex z_Hm])
             next
              assume z_Hey:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
              show FALSE
              by (rule notE [OF z_Hey z_Hn])
             qed
            qed
           qed
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 986"; *} qed
lemma ob'1070:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'55: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'56: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'70: "(\<exists> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = ([(a_VARIABLEunde_A3unde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"
assumes v'71: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''d'')))"
assumes v'72: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''c'')])))"
assumes v'73: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'74: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'75: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'76: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = (a_VARIABLEunde_knownunde_a)))"
assumes v'77: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = (a_VARIABLEunde_notKnownunde_a)))"
assumes v'78: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = (a_VARIABLEunde_lnbpartunde_a)))"
assumes v'79: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'80: "((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))"
assumes v'81: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
shows "(\<exists> a_CONSTANTunde_junde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = ([(a_VARIABLEunde_A3unde_a) EXCEPT ![(a_CONSTANTunde_junde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"(is "PROP ?ob'1070")
proof -
ML_command {* writeln "*** TLAPS ENTER 1070"; *}
show "PROP ?ob'1070"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_566056.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_566056.znn.out
;; obligation #1070
$hyp "v'55" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'56" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'70" (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (= a_VARIABLEunde_A3unde_hash_primea
(TLA.except a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
$hyp "v'71" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"d")
$hyp "v'72" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "c"))
$hyp "v'73" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'74" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'75" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'76" (= a_VARIABLEunde_knownunde_hash_primea
a_VARIABLEunde_knownunde_a)
$hyp "v'77" (= a_VARIABLEunde_notKnownunde_hash_primea
a_VARIABLEunde_notKnownunde_a)
$hyp "v'78" (= a_VARIABLEunde_lnbpartunde_hash_primea
a_VARIABLEunde_lnbpartunde_a)
$hyp "v'79" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'80" (= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)
$hyp "v'81" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$goal (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_junde_a) (= a_VARIABLEunde_A3unde_hash_primea
(TLA.except a_VARIABLEunde_A3unde_a a_CONSTANTunde_junde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bEx((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_hash_primea=except(a_VARIABLEunde_A3unde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a])))))" (is "?z_hd")
 using v'70 by blast
 assume z_Hp:"(~?z_hd)"
 show FALSE
 by (rule notE [OF z_Hp z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1070"; *} qed
lemma ob'1109:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
assumes v'55: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'56: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'70: "(\<exists> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = ([(a_VARIABLEunde_A3unde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"
assumes v'71: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''d'')))"
assumes v'72: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''c'')])))"
assumes v'73: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'74: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'75: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'76: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = (a_VARIABLEunde_knownunde_a)))"
assumes v'77: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = (a_VARIABLEunde_notKnownunde_a)))"
assumes v'78: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = (a_VARIABLEunde_lnbpartunde_a)))"
assumes v'79: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'80: "((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))"
assumes v'81: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h0806c :: c)))"
fixes a_CONSTANTunde_waunde_a
assumes a_CONSTANTunde_waunde_a_in : "(a_CONSTANTunde_waunde_a \<in> ((a_h68829a :: c)))"
assumes v'93: "(((a_CONSTANTunde_Punde_a) = ((h6db5c ((a_CONSTANTunde_waunde_a)) :: c))))"
shows "(\<exists> a_CONSTANTunde_junde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = ([(a_VARIABLEunde_A3unde_a) EXCEPT ![(a_CONSTANTunde_junde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"(is "PROP ?ob'1109")
proof -
ML_command {* writeln "*** TLAPS ENTER 1109"; *}
show "PROP ?ob'1109"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_a72e22.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_a72e22.znn.out
;; obligation #1109
$hyp "v'55" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'56" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'70" (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (= a_VARIABLEunde_A3unde_hash_primea
(TLA.except a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
$hyp "v'71" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"d")
$hyp "v'72" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "c"))
$hyp "v'73" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'74" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'75" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'76" (= a_VARIABLEunde_knownunde_hash_primea
a_VARIABLEunde_knownunde_a)
$hyp "v'77" (= a_VARIABLEunde_notKnownunde_hash_primea
a_VARIABLEunde_notKnownunde_a)
$hyp "v'78" (= a_VARIABLEunde_lnbpartunde_hash_primea
a_VARIABLEunde_lnbpartunde_a)
$hyp "v'79" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'80" (= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)
$hyp "v'81" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h0806c)
$hyp "a_CONSTANTunde_waunde_a_in" (TLA.in a_CONSTANTunde_waunde_a a_h68829a)
$hyp "v'93" (= a_CONSTANTunde_Punde_a
(h6db5c a_CONSTANTunde_waunde_a))
$goal (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_junde_a) (= a_VARIABLEunde_A3unde_hash_primea
(TLA.except a_VARIABLEunde_A3unde_a a_CONSTANTunde_junde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bEx((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_hash_primea=except(a_VARIABLEunde_A3unde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a])))))" (is "?z_hd")
 using v'70 by blast
 assume z_Hs:"(~?z_hd)"
 show FALSE
 by (rule notE [OF z_Hs z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1109"; *} qed
lemma ob'1434:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'72: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'73: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'76: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'82: "(\<exists> a_CONSTANTunde_Punde_a \<in> (subsetOf(((SUBSET (a_CONSTANTunde_Procunde_a))), %a_CONSTANTunde_Qunde_a. ((((a_CONSTANTunde_punde_a) \<in> (a_CONSTANTunde_Qunde_a))) & (\<forall> a_CONSTANTunde_punde_a_1 \<in> (((a_CONSTANTunde_Procunde_a) \\ ({(a_CONSTANTunde_punde_a)}))) : (((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a_1)))))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_Qunde_a)))))) | (((a_CONSTANTunde_Qunde_a) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a_1)))))))))) : ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (a_CONSTANTunde_Punde_a)]))))"
assumes v'83: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'84: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = ([(a_VARIABLEunde_A2unde_a) EXCEPT ![((arith_add (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))))), ((minus (((Succ[0]))))))))] = (fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))"
assumes v'85: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')])))"
assumes v'86: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'87: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'88: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = (a_VARIABLEunde_knownunde_a)))"
assumes v'89: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = (a_VARIABLEunde_notKnownunde_a)))"
assumes v'90: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = (a_VARIABLEunde_lnbpartunde_a)))"
assumes v'91: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'92: "((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))"
assumes v'93: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
assumes v'97: "((\<And> a_CONSTANTunde_qunde_a :: c. a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a) \<Longrightarrow> (((fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_qunde_a))) = (fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_qunde_a)))))))"
shows "(((a_ACTIONunde_Sexcl_BigNextunde_a) \<or> (((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a))) & ((([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]) = ([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))]))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a))))))"(is "PROP ?ob'1434")
proof -
ML_command {* writeln "*** TLAPS ENTER 1434"; *}
show "PROP ?ob'1434"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_07b639.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_07b639.znn.out
;; obligation #1434
$hyp "v'72" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'73" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'76" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'82" (TLA.bEx (TLA.subsetOf (TLA.SUBSET a_CONSTANTunde_Procunde_a) ((a_CONSTANTunde_Qunde_a) (/\ (TLA.in a_CONSTANTunde_punde_a
a_CONSTANTunde_Qunde_a) (TLA.bAll (TLA.setminus a_CONSTANTunde_Procunde_a
(TLA.set a_CONSTANTunde_punde_a)) ((a_CONSTANTunde_punde_a_1) (\/ (-. (= (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a_1))
(a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_Qunde_a)))
(= a_CONSTANTunde_Qunde_a
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a_1)))))))) ((a_CONSTANTunde_Punde_a) (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a a_CONSTANTunde_Punde_a))))
$hyp "v'83" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'84" (= a_VARIABLEunde_A2unde_hash_primea
(TLA.except a_VARIABLEunde_A2unde_a (arith.add (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a))
(arith.minus (TLA.fapply TLA.Succ 0))) (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a)))
$hyp "v'85" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
$hyp "v'86" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'87" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'88" (= a_VARIABLEunde_knownunde_hash_primea
a_VARIABLEunde_knownunde_a)
$hyp "v'89" (= a_VARIABLEunde_notKnownunde_hash_primea
a_VARIABLEunde_notKnownunde_a)
$hyp "v'90" (= a_VARIABLEunde_lnbpartunde_hash_primea
a_VARIABLEunde_lnbpartunde_a)
$hyp "v'91" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'92" (= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)
$hyp "v'93" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "v'97" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_qunde_a) (= (TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") ))) a_CONSTANTunde_qunde_a)
(TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))) a_CONSTANTunde_qunde_a))))
$goal (\/ a_ACTIONunde_Sexcl_BigNextunde_a
(/\ (= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)
(= (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") )))
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))))
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ho:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'93 by blast
 have z_Hn:"(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)"
 using v'92 by blast
 have z_Hi:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'87 by blast
 have z_Hp:"bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_qunde_a. ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[a_CONSTANTunde_qunde_a])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[a_CONSTANTunde_qunde_a]))))" (is "?z_hp")
 using v'97 by blast
 assume z_Hq:"(~(a_ACTIONunde_Sexcl_BigNextunde_a|((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&((a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)&((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))=Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))))&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a))))))" (is "~(_|?z_hcu)")
 have z_Hcy_z_Hp: "(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[x])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[x])))) == ?z_hp" (is "?z_hcy == _")
 by (unfold bAll_def)
 have z_Hcy: "?z_hcy" (is "\\A x : ?z_hdf(x)")
 by (unfold z_Hcy_z_Hp, fact z_Hp)
 have z_Hdg: "(~?z_hcu)" (is "~(?z_hi&?z_hcv)")
 by (rule zenon_notor_1 [OF z_Hq])
 show FALSE
 proof (rule zenon_notand [OF z_Hdg])
  assume z_Hdh:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
  show FALSE
  by (rule notE [OF z_Hdh z_Hi])
 next
  assume z_Hdi:"(~?z_hcv)" (is "~(?z_hn&?z_hcw)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdi])
   assume z_Hdj:"(a_VARIABLEunde_nextoutunde_hash_primea~=a_VARIABLEunde_nextoutunde_a)"
   show FALSE
   by (rule notE [OF z_Hdj z_Hn])
  next
   assume z_Hdk:"(~?z_hcw)" (is "~(?z_hcx&?z_ho)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdk])
    assume z_Hdl:"(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))~=Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))))" (is "?z_hbb~=?z_hcd")
    have z_Hdm: "(~(((isAFcn(?z_hbb)&isAFcn(?z_hcd))&(DOMAIN(?z_hbb)=DOMAIN(?z_hcd)))&(\\A zenon_Vna:((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna]))))))" (is "~(?z_hdo&?z_hdv)")
    by (rule zenon_notfunequal_0 [of "?z_hbb" "?z_hcd", OF z_Hdl])
    show FALSE
    proof (rule zenon_notand [OF z_Hdm])
     assume z_Hec:"(~?z_hdo)" (is "~(?z_hdp&?z_hds)")
     show FALSE
     proof (rule zenon_notand [OF z_Hec])
      assume z_Hed:"(~?z_hdp)" (is "~(?z_hdq&?z_hdr)")
      show FALSE
      proof (rule zenon_notand [OF z_Hed])
       assume z_Hee:"(~?z_hdq)"
       show FALSE
       by (rule zenon_notisafcn_fcn [of "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B'')))", OF z_Hee])
      next
       assume z_Hef:"(~?z_hdr)"
       show FALSE
       by (rule zenon_notisafcn_fcn [of "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))", OF z_Hef])
      qed
     next
      assume z_Heg:"(DOMAIN(?z_hbb)~=DOMAIN(?z_hcd))" (is "?z_hdt~=?z_hdu")
      have z_Heh: "(a_CONSTANTunde_Procunde_a~=?z_hdu)"
      by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vfaa. (zenon_Vfaa~=?z_hdu))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B'')))", OF z_Heg])
      have z_Hel: "(a_CONSTANTunde_Procunde_a~=a_CONSTANTunde_Procunde_a)"
      by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vhaa. (a_CONSTANTunde_Procunde_a~=zenon_Vhaa))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))", OF z_Heh])
      show FALSE
      by (rule zenon_noteq [OF z_Hel])
     qed
    next
     assume z_Hep:"(~?z_hdv)" (is "~(\\A x : ?z_heq(x))")
     have z_Her: "(\\E zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna])))))" (is "\\E x : ?z_het(x)")
     by (rule zenon_notallex_0 [of "?z_heq", OF z_Hep])
     have z_Heu: "?z_het((CHOOSE zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna]))))))" (is "~(?z_hew=>?z_hex)")
     by (rule zenon_ex_choose_0 [of "?z_het", OF z_Her])
     have z_Hew: "?z_hew"
     by (rule zenon_notimply_0 [OF z_Heu])
     have z_Hey: "((?z_hbb[(CHOOSE zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna])))))])~=(?z_hcd[(CHOOSE zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna])))))]))" (is "?z_hez~=?z_hfa")
     by (rule zenon_notimply_1 [OF z_Heu])
     have z_Hfb: "((CHOOSE zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna]))))) \\in a_CONSTANTunde_Procunde_a)" (is "?z_hfb")
     by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vig. ((CHOOSE zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna]))))) \\in zenon_Vig))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))", OF z_Hew])
     have z_Hff: "?z_hdf((CHOOSE zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna]))))))"
     by (rule zenon_all_0 [of "?z_hdf" "(CHOOSE zenon_Vna:(~((zenon_Vna \\in DOMAIN(?z_hcd))=>((?z_hbb[zenon_Vna])=(?z_hcd[zenon_Vna])))))", OF z_Hcy])
     show FALSE
     proof (rule zenon_imply [OF z_Hff])
      assume z_Hfg:"(~?z_hfb)"
      show FALSE
      by (rule notE [OF z_Hfg z_Hfb])
     next
      assume z_Hex:"?z_hex"
      show FALSE
      by (rule notE [OF z_Hey z_Hex])
     qed
    qed
   next
    assume z_Hfh:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
    show FALSE
    by (rule notE [OF z_Hfh z_Ho])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1434"; *} qed
lemma ob'1531:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'85: "((a_ACTIONunde_bunde_a ((a_CONSTANTunde_punde_a))))"
assumes v'92: "(((fapply ((a_STATEunde_pcBarunde_a), (a_CONSTANTunde_punde_a))) = (''A'')))"
assumes v'93: "((((a_h8b086a :: c)) = ([(a_STATEunde_pcBarunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''B'')])))"
assumes v'94: "(\<exists> a_CONSTANTunde_vunde_a \<in> (a_CONSTANTunde_Valunde_a) : ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = ([(a_VARIABLEunde_myValsunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<union> ({(a_CONSTANTunde_vunde_a)})))]))))"
assumes v'95: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
assumes v'96: "((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))"
shows "((((fapply ((a_STATEunde_pcBarunde_a), (a_CONSTANTunde_punde_a))) = (''A''))) & (\<exists> a_CONSTANTunde_vunde_a \<in> (a_CONSTANTunde_Valunde_a) : ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = ([(a_VARIABLEunde_myValsunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<union> ({(a_CONSTANTunde_vunde_a)})))])))) & ((((a_h8b086a :: c)) = ([(a_STATEunde_pcBarunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''B'')]))) & (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'1531")
proof -
ML_command {* writeln "*** TLAPS ENTER 1531"; *}
show "PROP ?ob'1531"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_ee2e62.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_ee2e62.znn.out
;; obligation #1531
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'85" (a_ACTIONunde_bunde_a a_CONSTANTunde_punde_a)
$hyp "v'92" (= (TLA.fapply a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a)
"A")
$hyp "v'93" (= a_h8b086a
(TLA.except a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a "B"))
$hyp "v'94" (TLA.bEx a_CONSTANTunde_Valunde_a ((a_CONSTANTunde_vunde_a) (= a_VARIABLEunde_myValsunde_hash_primea
(TLA.except a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
(TLA.set a_CONSTANTunde_vunde_a))))))
$hyp "v'95" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "v'96" (= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)
$goal (/\ (= (TLA.fapply a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a) "A")
(TLA.bEx a_CONSTANTunde_Valunde_a ((a_CONSTANTunde_vunde_a) (= a_VARIABLEunde_myValsunde_hash_primea
(TLA.except a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
(TLA.set a_CONSTANTunde_vunde_a)))))) (= a_h8b086a
(TLA.except a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a "B"))
(/\ (= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_STATEunde_pcBarunde_a[a_CONSTANTunde_punde_a])=''A'')" (is "?z_hk=?z_hn")
 using v'92 by blast
 have z_Hg:"bEx(a_CONSTANTunde_Valunde_a, (\<lambda>a_CONSTANTunde_vunde_a. (a_VARIABLEunde_myValsunde_hash_primea=except(a_VARIABLEunde_myValsunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_myValsunde_a[a_CONSTANTunde_punde_a]) \\cup {a_CONSTANTunde_vunde_a})))))" (is "?z_hg")
 using v'94 by blast
 have z_Hf:"(a_h8b086a=except(a_STATEunde_pcBarunde_a, a_CONSTANTunde_punde_a, ''B''))" (is "_=?z_hz")
 using v'93 by blast
 have z_Hi:"(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)"
 using v'96 by blast
 have z_Hh:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'95 by blast
 assume z_Hj:"(~((?z_hk=?z_hn)&(?z_hg&((a_h8b086a=?z_hz)&((a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a))))))" (is "~(?z_he&?z_hbg)")
 show FALSE
 proof (rule zenon_notand [OF z_Hj])
  assume z_Hbj:"(?z_hk~=?z_hn)"
  show FALSE
  by (rule notE [OF z_Hbj z_He])
 next
  assume z_Hbk:"(~?z_hbg)" (is "~(_&?z_hbh)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbk])
   assume z_Hbl:"(~?z_hg)"
   show FALSE
   by (rule notE [OF z_Hbl z_Hg])
  next
   assume z_Hbm:"(~?z_hbh)" (is "~(?z_hf&?z_hbi)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbm])
    assume z_Hbn:"(a_h8b086a~=?z_hz)"
    show FALSE
    by (rule notE [OF z_Hbn z_Hf])
   next
    assume z_Hbo:"(~?z_hbi)" (is "~(?z_hi&?z_hh)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbo])
     assume z_Hbp:"(a_VARIABLEunde_nextoutunde_hash_primea~=a_VARIABLEunde_nextoutunde_a)"
     show FALSE
     by (rule notE [OF z_Hbp z_Hi])
    next
     assume z_Hbq:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
     show FALSE
     by (rule notE [OF z_Hbq z_Hh])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1531"; *} qed
lemma ob'1551:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'85: "(\<exists> a_CONSTANTunde_vunde_a \<in> (a_CONSTANTunde_Valunde_a) : ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = ([(a_VARIABLEunde_myValsunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<union> ({(a_CONSTANTunde_vunde_a)})))]))))"
assumes v'86: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b'')))"
assumes v'87: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply (((a_VARIABLEunde_myValsunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<union> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))])))"
assumes v'88: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_nbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))])))"
assumes v'89: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''c'')])))"
assumes v'90: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'91: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'92: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'93: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = (a_VARIABLEunde_notKnownunde_a)))"
assumes v'94: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = (a_VARIABLEunde_lnbpartunde_a)))"
assumes v'95: "((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))"
assumes v'96: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
shows "(\<exists> a_CONSTANTunde_vunde_a \<in> (a_CONSTANTunde_Valunde_a) : ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = ([(a_VARIABLEunde_myValsunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<union> ({(a_CONSTANTunde_vunde_a)})))]))))"(is "PROP ?ob'1551")
proof -
ML_command {* writeln "*** TLAPS ENTER 1551"; *}
show "PROP ?ob'1551"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_a8db57.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_a8db57.znn.out
;; obligation #1551
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'85" (TLA.bEx a_CONSTANTunde_Valunde_a ((a_CONSTANTunde_vunde_a) (= a_VARIABLEunde_myValsunde_hash_primea
(TLA.except a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
(TLA.set a_CONSTANTunde_vunde_a))))))
$hyp "v'86" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
$hyp "v'87" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_myValsunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))
$hyp "v'88" (= a_VARIABLEunde_nbpartunde_hash_primea
(TLA.except a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a (a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))))
$hyp "v'89" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "c"))
$hyp "v'90" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'91" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'92" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'93" (= a_VARIABLEunde_notKnownunde_hash_primea
a_VARIABLEunde_notKnownunde_a)
$hyp "v'94" (= a_VARIABLEunde_lnbpartunde_hash_primea
a_VARIABLEunde_lnbpartunde_a)
$hyp "v'95" (= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)
$hyp "v'96" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$goal (TLA.bEx a_CONSTANTunde_Valunde_a ((a_CONSTANTunde_vunde_a) (= a_VARIABLEunde_myValsunde_hash_primea
(TLA.except a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
(TLA.set a_CONSTANTunde_vunde_a))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bEx(a_CONSTANTunde_Valunde_a, (\<lambda>a_CONSTANTunde_vunde_a. (a_VARIABLEunde_myValsunde_hash_primea=except(a_VARIABLEunde_myValsunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_myValsunde_a[a_CONSTANTunde_punde_a]) \\cup {a_CONSTANTunde_vunde_a})))))" (is "?z_hd")
 using v'85 by blast
 assume z_Hp:"(~?z_hd)"
 show FALSE
 by (rule notE [OF z_Hp z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1551"; *} qed
lemma ob'1570:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'73: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'74: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'77: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'85: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'86: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'87: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'88: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'89: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'90: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'91: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'92: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'93: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'94: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'95: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
assumes v'104: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({})))"
shows "((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c''))) & ((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a))) & (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) & ((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a))) & ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a))) & ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'1570")
proof -
ML_command {* writeln "*** TLAPS ENTER 1570"; *}
show "PROP ?ob'1570"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_5a06a3.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_5a06a3.znn.out
;; obligation #1570
$hyp "v'73" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'74" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'77" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'85" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'86" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'87" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'88" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'89" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'90" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'91" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'92" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'93" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'94" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'95" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "v'104" (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset))
$goal (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "c")
(= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)
(/\ (= a_VARIABLEunde_resultunde_hash_primea a_VARIABLEunde_resultunde_a)
(= a_VARIABLEunde_A2unde_hash_primea a_VARIABLEunde_A2unde_a)
(= a_VARIABLEunde_A3unde_hash_primea a_VARIABLEunde_A3unde_a)
(= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_nbpartunde_hash_primea a_VARIABLEunde_nbpartunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''c'')" (is "?z_hq=?z_ht")
 using v'86 by blast
 have z_Hf:"(a_VARIABLEunde_lnbpartunde_hash_primea=except(a_VARIABLEunde_lnbpartunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])))" (is "_=?z_hv")
 using v'87 by blast
 have z_Hg:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hba")
 using v'88 by blast
 have z_Hh:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, ((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]) +  -.(1))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hbm")
 using v'89 by blast
 have z_Ho:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hbx~=_")
 using v'104 by blast
 have z_Hd:"cond((?z_hbx~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)), (cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))))" (is "?z_hd")
 using v'85 by blast
 have z_Hi:"(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)"
 using v'90 by blast
 have z_Hj:"(a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)"
 using v'91 by blast
 have z_Hk:"(a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)"
 using v'92 by blast
 have z_Hl:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'93 by blast
 have z_Hm:"(a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)"
 using v'94 by blast
 have z_Hn:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'95 by blast
 assume z_Hp:"(~((?z_hq=?z_ht)&((a_VARIABLEunde_lnbpartunde_hash_primea=?z_hv)&((a_VARIABLEunde_knownunde_hash_primea=?z_hba)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbm)&((?z_hbx~={})&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&((a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)&((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)&((a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)&((a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)&((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&((a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a))))))))))))))" (is "~(?z_he&?z_hdh)")
 show FALSE
 proof (rule zenon_notand [OF z_Hp])
  assume z_Hds:"(?z_hq~=?z_ht)"
  show FALSE
  by (rule notE [OF z_Hds z_He])
 next
  assume z_Hdt:"(~?z_hdh)" (is "~(?z_hf&?z_hdi)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdt])
   assume z_Hdu:"(a_VARIABLEunde_lnbpartunde_hash_primea~=?z_hv)"
   show FALSE
   by (rule notE [OF z_Hdu z_Hf])
  next
   assume z_Hdv:"(~?z_hdi)" (is "~(?z_hg&?z_hdj)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdv])
    assume z_Hdw:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hba)"
    show FALSE
    by (rule notE [OF z_Hdw z_Hg])
   next
    assume z_Hdx:"(~?z_hdj)" (is "~(?z_hh&?z_hdk)")
    show FALSE
    proof (rule zenon_notand [OF z_Hdx])
     assume z_Hdy:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbm)"
     show FALSE
     by (rule notE [OF z_Hdy z_Hh])
    next
     assume z_Hdz:"(~?z_hdk)" (is "~(?z_ho&?z_hdl)")
     show FALSE
     proof (rule zenon_notand [OF z_Hdz])
      assume z_Hea:"(~?z_ho)" (is "~~?z_heb")
      show FALSE
      by (rule notE [OF z_Hea z_Ho])
     next
      assume z_Hec:"(~?z_hdl)" (is "~(?z_hca&?z_hdm)")
      show FALSE
      proof (rule zenon_notand [OF z_Hec])
       assume z_Hed:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))" (is "_~=?z_hcc")
       show FALSE
       proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_ho" "(?z_hca&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" "(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
        assume z_Ho:"?z_ho"
        assume z_Hbz:"(?z_hca&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "_&?z_hce")
        have z_Hca: "?z_hca"
        by (rule zenon_and_0 [OF z_Hbz])
        show FALSE
        by (rule notE [OF z_Hed z_Hca])
       next
        assume z_Hea:"(~?z_ho)" (is "~~?z_heb")
        assume z_Hch:"(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hci&?z_hcu")
        show FALSE
        by (rule notE [OF z_Hea z_Ho])
       qed
      next
       assume z_Heg:"(~?z_hdm)" (is "~(?z_hce&?z_hdn)")
       show FALSE
       proof (rule zenon_notand [OF z_Heg])
        assume z_Heh:"(a_VARIABLEunde_nextoutunde_hash_primea~=a_VARIABLEunde_nextoutunde_a)"
        show FALSE
        proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_ho" "(?z_hca&?z_hce)" "(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hce))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
         assume z_Ho:"?z_ho"
         assume z_Hbz:"(?z_hca&?z_hce)"
         have z_Hce: "?z_hce"
         by (rule zenon_and_1 [OF z_Hbz])
         show FALSE
         by (rule notE [OF z_Heh z_Hce])
        next
         assume z_Hea:"(~?z_ho)" (is "~~?z_heb")
         assume z_Hch:"(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a])))))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hce))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hci&?z_hcu")
         show FALSE
         by (rule notE [OF z_Hea z_Ho])
        qed
       next
        assume z_Hei:"(~?z_hdn)" (is "~(?z_hi&?z_hdo)")
        show FALSE
        proof (rule zenon_notand [OF z_Hei])
         assume z_Hej:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
         show FALSE
         by (rule notE [OF z_Hej z_Hi])
        next
         assume z_Hek:"(~?z_hdo)" (is "~(?z_hj&?z_hdp)")
         show FALSE
         proof (rule zenon_notand [OF z_Hek])
          assume z_Hel:"(a_VARIABLEunde_A2unde_hash_primea~=a_VARIABLEunde_A2unde_a)"
          show FALSE
          by (rule notE [OF z_Hel z_Hj])
         next
          assume z_Hem:"(~?z_hdp)" (is "~(?z_hk&?z_hdq)")
          show FALSE
          proof (rule zenon_notand [OF z_Hem])
           assume z_Hen:"(a_VARIABLEunde_A3unde_hash_primea~=a_VARIABLEunde_A3unde_a)"
           show FALSE
           by (rule notE [OF z_Hen z_Hk])
          next
           assume z_Heo:"(~?z_hdq)" (is "~(?z_hl&?z_hdr)")
           show FALSE
           proof (rule zenon_notand [OF z_Heo])
            assume z_Hep:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
            show FALSE
            by (rule notE [OF z_Hep z_Hl])
           next
            assume z_Heq:"(~?z_hdr)" (is "~(?z_hm&?z_hn)")
            show FALSE
            proof (rule zenon_notand [OF z_Heq])
             assume z_Her:"(a_VARIABLEunde_nbpartunde_hash_primea~=a_VARIABLEunde_nbpartunde_a)"
             show FALSE
             by (rule notE [OF z_Her z_Hm])
            next
             assume z_Hes:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
             show FALSE
             by (rule notE [OF z_Hes z_Hn])
            qed
           qed
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1570"; *} qed
lemma ob'1574:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'86: "((a_ACTIONunde_cunde_a ((a_CONSTANTunde_punde_a))))"
assumes v'97: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'98: "(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''d'')))"
assumes v'99: "(((fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_punde_a))) = (fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_punde_a)))))"
assumes v'100: "(\<forall> a_CONSTANTunde_qunde_a \<in> (((a_CONSTANTunde_Procunde_a) \\ ({(a_CONSTANTunde_punde_a)}))) : (((fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_qunde_a))) = (fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_qunde_a))))))"
shows "((([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]) = ([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))])))"(is "PROP ?ob'1574")
proof -
ML_command {* writeln "*** TLAPS ENTER 1574"; *}
show "PROP ?ob'1574"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_ab7812.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_ab7812.znn.out
;; obligation #1574
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'86" (a_ACTIONunde_cunde_a a_CONSTANTunde_punde_a)
$hyp "v'97" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'98" (= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a)
"d")
$hyp "v'99" (= (TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") ))) a_CONSTANTunde_punde_a)
(TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))) a_CONSTANTunde_punde_a))
$hyp "v'100" (TLA.bAll (TLA.setminus a_CONSTANTunde_Procunde_a
(TLA.set a_CONSTANTunde_punde_a)) ((a_CONSTANTunde_qunde_a) (= (TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") ))) a_CONSTANTunde_qunde_a)
(TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))) a_CONSTANTunde_qunde_a))))
$goal (= (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") )))
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[a_CONSTANTunde_qunde_a])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[a_CONSTANTunde_qunde_a]))))" (is "?z_hh")
 using v'100 by blast
 have z_Hc:"(a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hc")
 using a_CONSTANTunde_punde_a_in by blast
 have z_He:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''c'')" (is "?z_hch=?z_hbd")
 using v'97 by blast
 have z_Hf:"((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a])=''d'')" (is "?z_hci=?z_hbe")
 using v'98 by blast
 have z_Hg:"((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[a_CONSTANTunde_punde_a])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[a_CONSTANTunde_punde_a]))" (is "?z_hcj=?z_hck")
 using v'99 by blast
 have zenon_L1_: "(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[x])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[x])))) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))~=a_CONSTANTunde_punde_a) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a) ==> ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])) ==> FALSE" (is "?z_hcl ==> ?z_hcs ==> ?z_hdc ==> ?z_hdd ==> FALSE")
 proof -
  assume z_Hcl:"?z_hcl" (is "\\A x : ?z_hdg(x)")
  assume z_Hcs:"?z_hcs" (is "?z_hct~=_")
  assume z_Hdc:"?z_hdc"
  assume z_Hdd:"?z_hdd" (is "?z_hde~=?z_hdf")
  have z_Hdh: "?z_hdg(?z_hct)" (is "?z_hdi=>?z_hdj")
  by (rule zenon_all_0 [of "?z_hdg" "?z_hct", OF z_Hcl])
  show FALSE
  proof (rule zenon_imply [OF z_Hdh])
   assume z_Hdk:"(~?z_hdi)"
   show FALSE
   proof (rule zenon_notin_setminus [of "?z_hct" "a_CONSTANTunde_Procunde_a" "{a_CONSTANTunde_punde_a}", OF z_Hdk])
    assume z_Hdl:"(~?z_hdc)"
    show FALSE
    by (rule notE [OF z_Hdl z_Hdc])
   next
    assume z_Hdm:"(?z_hct \\in {a_CONSTANTunde_punde_a})" (is "?z_hdm")
    show FALSE
    proof (rule zenon_in_addElt [of "?z_hct" "a_CONSTANTunde_punde_a" "{}", OF z_Hdm])
     assume z_Hdo:"(?z_hct=a_CONSTANTunde_punde_a)"
     show FALSE
     by (rule notE [OF z_Hcs z_Hdo])
    next
     assume z_Hdp:"(?z_hct \\in {})" (is "?z_hdp")
     show FALSE
     by (rule zenon_in_emptyset [of "?z_hct", OF z_Hdp])
    qed
   qed
  next
   assume z_Hdj:"?z_hdj"
   show FALSE
   by (rule notE [OF z_Hdd z_Hdj])
  qed
 qed
 have zenon_L2_: "((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=?z_hci) ==> ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a) ==> (\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[x])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[x])))) ==> FALSE" (is "?z_hdq ==> ?z_hdd ==> ?z_hdc ==> ?z_hcl ==> FALSE")
 proof -
  assume z_Hdq:"?z_hdq" (is "?z_hdr~=_")
  assume z_Hdd:"?z_hdd" (is "?z_hde~=?z_hdf")
  assume z_Hdc:"?z_hdc"
  assume z_Hcl:"?z_hcl" (is "\\A x : ?z_hdg(x)")
  show FALSE
  proof (rule zenon_noteq [of "?z_hci"])
   have z_Hdo: "((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))=a_CONSTANTunde_punde_a)" (is "?z_hct=_")
   proof (rule zenon_nnpp [of "(?z_hct=a_CONSTANTunde_punde_a)"])
    assume z_Hcs:"(?z_hct~=a_CONSTANTunde_punde_a)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hcl z_Hcs z_Hdc z_Hdd])
   qed
   have z_Hds: "(?z_hci~=?z_hci)"
   by (rule subst [where P="(\<lambda>zenon_Vaq. ((a_VARIABLEunde_pcunde_hash_primea[zenon_Vaq])~=?z_hci))", OF z_Hdo], fact z_Hdq)
   thus "(?z_hci~=?z_hci)" .
  qed
 qed
 have zenon_L3_: "((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=?z_hch) ==> ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a) ==> (\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[x])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[x])))) ==> FALSE" (is "?z_hdx ==> ?z_hdd ==> ?z_hdc ==> ?z_hcl ==> FALSE")
 proof -
  assume z_Hdx:"?z_hdx" (is "?z_hdy~=_")
  assume z_Hdd:"?z_hdd" (is "?z_hde~=?z_hdf")
  assume z_Hdc:"?z_hdc"
  assume z_Hcl:"?z_hcl" (is "\\A x : ?z_hdg(x)")
  show FALSE
  proof (rule zenon_noteq [of "?z_hch"])
   have z_Hdo: "((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))=a_CONSTANTunde_punde_a)" (is "?z_hct=_")
   proof (rule zenon_nnpp [of "(?z_hct=a_CONSTANTunde_punde_a)"])
    assume z_Hcs:"(?z_hct~=a_CONSTANTunde_punde_a)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hcl z_Hcs z_Hdc z_Hdd])
   qed
   have z_Hdz: "(?z_hch~=?z_hch)"
   by (rule subst [where P="(\<lambda>zenon_Vbq. ((a_VARIABLEunde_pcunde_a[zenon_Vbq])~=?z_hch))", OF z_Hdo], fact z_Hdx)
   thus "(?z_hch~=?z_hch)" .
  qed
 qed
 have zenon_L4_: "(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[x])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[x])))) ==> (a_CONSTANTunde_punde_a~=(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a) ==> ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])) ==> FALSE" (is "?z_hcl ==> ?z_hee ==> ?z_hdc ==> ?z_hdd ==> FALSE")
 proof -
  assume z_Hcl:"?z_hcl" (is "\\A x : ?z_hdg(x)")
  assume z_Hee:"?z_hee" (is "_~=?z_hct")
  assume z_Hdc:"?z_hdc"
  assume z_Hdd:"?z_hdd" (is "?z_hde~=?z_hdf")
  have z_Hdh: "?z_hdg(?z_hct)" (is "?z_hdi=>?z_hdj")
  by (rule zenon_all_0 [of "?z_hdg" "?z_hct", OF z_Hcl])
  show FALSE
  proof (rule zenon_imply [OF z_Hdh])
   assume z_Hdk:"(~?z_hdi)"
   show FALSE
   proof (rule zenon_notin_setminus [of "?z_hct" "a_CONSTANTunde_Procunde_a" "{a_CONSTANTunde_punde_a}", OF z_Hdk])
    assume z_Hdl:"(~?z_hdc)"
    show FALSE
    by (rule notE [OF z_Hdl z_Hdc])
   next
    assume z_Hdm:"(?z_hct \\in {a_CONSTANTunde_punde_a})" (is "?z_hdm")
    show FALSE
    proof (rule zenon_in_addElt [of "?z_hct" "a_CONSTANTunde_punde_a" "{}", OF z_Hdm])
     assume z_Hdo:"(?z_hct=a_CONSTANTunde_punde_a)"
     show FALSE
     by (rule zenon_eqsym [OF z_Hdo z_Hee])
    next
     assume z_Hdp:"(?z_hct \\in {})" (is "?z_hdp")
     show FALSE
     by (rule zenon_in_emptyset [of "?z_hct", OF z_Hdp])
    qed
   qed
  next
   assume z_Hdj:"?z_hdj"
   show FALSE
   by (rule notE [OF z_Hdd z_Hdj])
  qed
 qed
 have zenon_L5_: "((?z_hch~=''e'')&((~(?z_hch \\in {?z_hbd, ?z_hbe}))&((~(?z_hch \\in {''a'', ''b''}))&TRUE))) ==> (?z_hch=?z_hbd) ==> FALSE" (is "?z_hef ==> ?z_he ==> FALSE")
 proof -
  assume z_Hef:"?z_hef" (is "?z_heg&?z_heh")
  assume z_He:"?z_he"
  have z_Heh: "?z_heh" (is "?z_hei&?z_hek")
  by (rule zenon_and_1 [OF z_Hef])
  have z_Hei: "?z_hei" (is "~?z_hej")
  by (rule zenon_and_0 [OF z_Heh])
  have z_Heo: "(?z_hch~=?z_hbd)"
  by (rule zenon_notin_addElt_0 [of "?z_hch" "?z_hbd" "{?z_hbe}", OF z_Hei])
  show FALSE
  by (rule notE [OF z_Heo z_He])
 qed
 assume z_Hi:"(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))~=Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))))" (is "?z_hq~=?z_hbs")
 have z_Hcl_z_Hh: "(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((?z_hq[x])=(?z_hbs[x])))) == ?z_hh" (is "?z_hcl == _")
 by (unfold bAll_def)
 have z_Hcl: "?z_hcl" (is "\\A x : ?z_hdg(x)")
 by (unfold z_Hcl_z_Hh, fact z_Hh)
 show FALSE
 proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vi. (zenon_Vi=?z_hck))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B'')))" "a_CONSTANTunde_punde_a", OF z_Hg])
  assume z_Het:"(~?z_hc)"
  show FALSE
  by (rule notE [OF z_Het z_Hc])
 next
  assume z_Heu:"((CASE (?z_hci \\in {''a'', ''b''}) -> ''A'' [] (?z_hci \\in {?z_hbd, ?z_hbe}) -> ''B'' [] (?z_hci=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))=?z_hck)" (is "?z_hev=_")
  show FALSE
  proof (rule zenon_case3 [of "(\<lambda>zenon_Vi. (zenon_Vi=?z_hck))", OF z_Heu])
   assume z_Hew:"(?z_hci \\in {''a'', ''b''})" (is "?z_hew")
   assume z_Hfc:"(''A''=?z_hck)" (is "?z_hba=_")
   show FALSE
   proof (rule zenon_in_addElt [of "?z_hci" "''a''" "{''b''}", OF z_Hew])
    assume z_Hfe:"(?z_hci=''a'')" (is "_=?z_hy")
    have z_Hff: "(?z_hy~=?z_hbe)"
    by auto
    have z_Hds: "(?z_hci~=?z_hci)"
    by (rule zenon_stringdiffll [OF z_Hff z_Hfe z_Hf])
     show FALSE
     by (rule zenon_noteq [OF z_Hds])
   next
    assume z_Hfg:"(?z_hci \\in {''b''})" (is "?z_hfg")
    show FALSE
    proof (rule zenon_in_addElt [of "?z_hci" "''b''" "{}", OF z_Hfg])
     assume z_Hfh:"(?z_hci=''b'')" (is "_=?z_hz")
     have z_Hfi: "(?z_hz~=?z_hbe)"
     by auto
     have z_Hds: "(?z_hci~=?z_hci)"
     by (rule zenon_stringdiffll [OF z_Hfi z_Hfh z_Hf])
      show FALSE
      by (rule zenon_noteq [OF z_Hds])
    next
     assume z_Hfj:"(?z_hci \\in {})" (is "?z_hfj")
     show FALSE
     by (rule zenon_in_emptyset [of "?z_hci", OF z_Hfj])
    qed
   qed
  next
   assume z_Hex:"(?z_hci \\in {?z_hbd, ?z_hbe})" (is "?z_hex")
   assume z_Hfk:"(''B''=?z_hck)" (is "?z_hbf=_")
   show FALSE
   proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vja. (?z_hbf=zenon_Vja))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf)))" "a_CONSTANTunde_punde_a", OF z_Hfk])
    assume z_Het:"(~?z_hc)"
    show FALSE
    by (rule notE [OF z_Het z_Hc])
   next
    assume z_Hfo:"(?z_hbf=(CASE (?z_hch \\in {''a'', ''b''}) -> ''A'' [] (?z_hch \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] (?z_hch=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf)))" (is "_=?z_hfp")
    show FALSE
    proof (rule zenon_case3 [of "(\<lambda>zenon_Vja. (?z_hbf=zenon_Vja))", OF z_Hfo])
     assume z_Hem:"(?z_hch \\in {''a'', ''b''})" (is "?z_hem")
     assume z_Hfu:"(?z_hbf=''A'')" (is "_=?z_hba")
     have z_Hfv: "(?z_hbf~=?z_hba)"
     by (simp only: zenon_sa_1 zenon_sa_2,
         ((rule zenon_sa_diff_2)+)?,
         (rule zenon_sa_diff_3, auto)?,
         (rule zenon_sa_diff_1, auto)?,
         (rule zenon_sa_diff_0a)?, (rule zenon_sa_diff_0b)?)
     show FALSE
     by (rule notE [OF z_Hfv z_Hfu])
    next
     assume z_Hej:"(?z_hch \\in {?z_hbd, ?z_hbe})" (is "?z_hej")
     assume z_Hfw:"(?z_hbf=?z_hbf)"
     have z_Hfx: "(~(((isAFcn(?z_hq)&isAFcn(?z_hbs))&(DOMAIN(?z_hq)=DOMAIN(?z_hbs)))&(\\A zenon_Vg:((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg]))))))" (is "~(?z_hfz&?z_hgf)")
     by (rule zenon_notfunequal_0 [of "?z_hq" "?z_hbs", OF z_Hi])
     show FALSE
     proof (rule zenon_notand [OF z_Hfx])
      assume z_Hgg:"(~?z_hfz)" (is "~(?z_hga&?z_hgd)")
      show FALSE
      proof (rule zenon_notand [OF z_Hgg])
       assume z_Hgh:"(~?z_hga)" (is "~(?z_hgb&?z_hgc)")
       show FALSE
       proof (rule zenon_notand [OF z_Hgh])
        assume z_Hgi:"(~?z_hgb)"
        show FALSE
        by (rule zenon_notisafcn_fcn [of "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ?z_hbf)))", OF z_Hgi])
       next
        assume z_Hgj:"(~?z_hgc)"
        show FALSE
        by (rule zenon_notisafcn_fcn [of "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf)))", OF z_Hgj])
       qed
      next
       assume z_Hgk:"(DOMAIN(?z_hq)~=DOMAIN(?z_hbs))" (is "?z_hge~=?z_hcy")
       have z_Hgl: "(a_CONSTANTunde_Procunde_a~=?z_hcy)"
       by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vip. (zenon_Vip~=?z_hcy))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ?z_hbf)))", OF z_Hgk])
       have z_Hgp: "(a_CONSTANTunde_Procunde_a~=a_CONSTANTunde_Procunde_a)"
       by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vkp. (a_CONSTANTunde_Procunde_a~=zenon_Vkp))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf)))", OF z_Hgl])
       show FALSE
       by (rule zenon_noteq [OF z_Hgp])
      qed
     next
      assume z_Hgt:"(~?z_hgf)" (is "~(\\A x : ?z_hgu(x))")
      have z_Hgv: "(\\E zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))" (is "\\E x : ?z_hgw(x)")
      by (rule zenon_notallex_0 [of "?z_hgu", OF z_Hgt])
      have z_Hgx: "?z_hgw((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg]))))))" (is "~(?z_hgy=>?z_hdj)")
      by (rule zenon_ex_choose_0 [of "?z_hgw", OF z_Hgv])
      have z_Hgy: "?z_hgy"
      by (rule zenon_notimply_0 [OF z_Hgx])
      have z_Hdd: "((?z_hq[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])~=(?z_hbs[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]))" (is "?z_hde~=?z_hdf")
      by (rule zenon_notimply_1 [OF z_Hgx])
      have z_Hdc: "((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a)" (is "?z_hdc")
      by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vuc. ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg]))))) \\in zenon_Vuc))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf)))", OF z_Hgy])
      show FALSE
      proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vsc. (zenon_Vsc~=?z_hdf))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ?z_hbf)))" "(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))", OF z_Hdd])
       assume z_Hdl:"(~?z_hdc)"
       show FALSE
       by (rule notE [OF z_Hdl z_Hdc])
      next
       assume z_Hhf:"((CASE ((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ?z_hbf))~=?z_hdf)" (is "?z_hhg~=_")
       show FALSE
       proof (rule zenon_case3 [of "(\<lambda>zenon_Vsc. (zenon_Vsc~=?z_hdf))", OF z_Hhf])
        assume z_Hhh:"((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''a'', ''b''})" (is "?z_hhh")
        assume z_Hhn:"(''A''~=?z_hdf)" (is "?z_hba~=_")
        show FALSE
        proof (rule zenon_in_addElt [of "(a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])" "''a''" "{''b''}", OF z_Hhh])
         assume z_Hho:"((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''a'')" (is "?z_hdr=?z_hy")
         have z_Hff: "(?z_hy~=?z_hbe)"
         by auto
         have z_Hdq: "(?z_hdr~=?z_hci)"
         by (rule zenon_stringdiffll [OF z_Hff z_Hho z_Hf])
          show FALSE
          by (rule zenon_L2_ [OF z_Hdq z_Hdd z_Hdc z_Hcl])
        next
         assume z_Hhp:"((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''b''})" (is "?z_hhp")
         show FALSE
         proof (rule zenon_in_addElt [of "(a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])" "''b''" "{}", OF z_Hhp])
          assume z_Hhq:"((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''b'')" (is "?z_hdr=?z_hz")
          have z_Hfi: "(?z_hz~=?z_hbe)"
          by auto
          have z_Hdq: "(?z_hdr~=?z_hci)"
          by (rule zenon_stringdiffll [OF z_Hfi z_Hhq z_Hf])
           show FALSE
           by (rule zenon_L2_ [OF z_Hdq z_Hdd z_Hdc z_Hcl])
         next
          assume z_Hhr:"((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {})" (is "?z_hhr")
          show FALSE
          by (rule zenon_in_emptyset [of "(a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])", OF z_Hhr])
         qed
        qed
       next
        assume z_Hhi:"((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {?z_hbd, ?z_hbe})" (is "?z_hhi")
        assume z_Hhs:"(?z_hbf~=?z_hdf)"
        show FALSE
        proof (rule zenon_fapplyfcn [of "(\<lambda>zenon_Vyf. (?z_hbf~=zenon_Vyf))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf)))" "(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))", OF z_Hhs])
         assume z_Hdl:"(~?z_hdc)"
         show FALSE
         by (rule notE [OF z_Hdl z_Hdc])
        next
         assume z_Hhw:"(?z_hbf~=(CASE ((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {?z_hbd, ?z_hbe}) -> ?z_hbf [] ((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf)))" (is "_~=?z_hhx")
         show FALSE
         proof (rule zenon_case3 [of "(\<lambda>zenon_Vyf. (?z_hbf~=zenon_Vyf))", OF z_Hhw])
          assume z_Hhy:"((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''a'', ''b''})" (is "?z_hhy")
          assume z_Hfv:"(?z_hbf~=''A'')" (is "_~=?z_hba")
          show FALSE
          proof (rule zenon_in_addElt [of "(a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])" "''a''" "{''b''}", OF z_Hhy])
           assume z_Hie:"((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''a'')" (is "?z_hdy=?z_hy")
           have z_Hif: "(?z_hy~=?z_hbd)"
           by auto
           have z_Hdx: "(?z_hdy~=?z_hch)"
           by (rule zenon_stringdiffll [OF z_Hif z_Hie z_He])
            show FALSE
            by (rule zenon_L3_ [OF z_Hdx z_Hdd z_Hdc z_Hcl])
          next
           assume z_Hig:"((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''b''})" (is "?z_hig")
           show FALSE
           proof (rule zenon_in_addElt [of "(a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])" "''b''" "{}", OF z_Hig])
            assume z_Hih:"((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''b'')" (is "?z_hdy=?z_hz")
            have z_Hii: "(?z_hz~=?z_hbd)"
            by auto
            have z_Hdx: "(?z_hdy~=?z_hch)"
            by (rule zenon_stringdiffll [OF z_Hii z_Hih z_He])
             show FALSE
             by (rule zenon_L3_ [OF z_Hdx z_Hdd z_Hdc z_Hcl])
           next
            assume z_Hij:"((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {})" (is "?z_hij")
            show FALSE
            by (rule zenon_in_emptyset [of "(a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])", OF z_Hij])
           qed
          qed
         next
          assume z_Hhz:"((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {?z_hbd, ?z_hbe})" (is "?z_hhz")
          assume z_Hik:"(?z_hbf~=?z_hbf)"
          show FALSE
          by (rule zenon_noteq [OF z_Hik])
         next
          assume z_Hia:"((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''e'')" (is "?z_hdy=?z_hbh")
          assume z_Hil:"(?z_hbf~=cond(((a_VARIABLEunde_lnbpartunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf))" (is "_~=?z_hib")
          have z_Him: "(?z_hbh~=?z_hbd)"
          by auto
          have z_Hdx: "(?z_hdy~=?z_hch)"
          by (rule zenon_stringdiffll [OF z_Him z_Hia z_He])
           show FALSE
           by (rule zenon_L3_ [OF z_Hdx z_Hdd z_Hdc z_Hcl])
         next
          assume z_Hin:"(((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])~=''e'')&((~((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {?z_hbd, ?z_hbe}))&((~((a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''a'', ''b''}))&TRUE)))" (is "?z_hio&?z_hip")
          have z_Hip: "?z_hip" (is "?z_hiq&?z_hir")
          by (rule zenon_and_1 [OF z_Hin])
          have z_Hiq: "?z_hiq" (is "~?z_hhz")
          by (rule zenon_and_0 [OF z_Hip])
          show FALSE
          proof (rule notE [OF z_Hiq])
           have z_Hit: "(?z_hch=(a_VARIABLEunde_pcunde_a[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]))" (is "_=?z_hdy")
           proof (rule zenon_nnpp [of "(?z_hch=?z_hdy)"])
            assume z_Hiu:"(?z_hch~=?z_hdy)"
            show FALSE
            proof (rule zenon_noteq [of "?z_hdy"])
             have z_Hiv: "(a_CONSTANTunde_punde_a=(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg]))))))" (is "_=?z_hct")
             proof (rule zenon_nnpp [of "(a_CONSTANTunde_punde_a=?z_hct)"])
              assume z_Hee:"(a_CONSTANTunde_punde_a~=?z_hct)"
              show FALSE
              by (rule zenon_L4_ [OF z_Hcl z_Hee z_Hdc z_Hdd])
             qed
             have z_Hiw: "(?z_hdy~=?z_hdy)"
             by (rule subst [where P="(\<lambda>zenon_Vcq. ((a_VARIABLEunde_pcunde_a[zenon_Vcq])~=?z_hdy))", OF z_Hiv], fact z_Hiu)
             thus "(?z_hdy~=?z_hdy)" .
            qed
           qed
           have z_Hhz: "?z_hhz"
           by (rule subst [where P="(\<lambda>zenon_Vdq. (zenon_Vdq \\in {?z_hbd, ?z_hbe}))", OF z_Hit], fact z_Hej)
           thus "?z_hhz" .
          qed
         qed
        qed
       next
        assume z_Hhj:"((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=''e'')" (is "?z_hdr=?z_hbh")
        assume z_Hje:"(cond(((a_VARIABLEunde_lnbpartunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ?z_hbf)~=?z_hdf)" (is "?z_hhk~=_")
        have z_Hjf: "(?z_hbh~=?z_hbe)"
        by auto
        have z_Hdq: "(?z_hdr~=?z_hci)"
        by (rule zenon_stringdiffll [OF z_Hjf z_Hhj z_Hf])
         show FALSE
         by (rule zenon_L2_ [OF z_Hdq z_Hdd z_Hdc z_Hcl])
       next
        assume z_Hjg:"(((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))])~=''e'')&((~((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {?z_hbd, ?z_hbe}))&((~((a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]) \\in {''a'', ''b''}))&TRUE)))" (is "?z_hjh&?z_hji")
        have z_Hji: "?z_hji" (is "?z_hjj&?z_hjk")
        by (rule zenon_and_1 [OF z_Hjg])
        have z_Hjj: "?z_hjj" (is "~?z_hhi")
        by (rule zenon_and_0 [OF z_Hji])
        show FALSE
        proof (rule notE [OF z_Hjj])
         have z_Hjm: "(?z_hci=(a_VARIABLEunde_pcunde_hash_primea[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg])))))]))" (is "_=?z_hdr")
         proof (rule zenon_nnpp [of "(?z_hci=?z_hdr)"])
          assume z_Hjn:"(?z_hci~=?z_hdr)"
          show FALSE
          proof (rule zenon_noteq [of "?z_hdr"])
           have z_Hiv: "(a_CONSTANTunde_punde_a=(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbs))=>((?z_hq[zenon_Vg])=(?z_hbs[zenon_Vg]))))))" (is "_=?z_hct")
           proof (rule zenon_nnpp [of "(a_CONSTANTunde_punde_a=?z_hct)"])
            assume z_Hee:"(a_CONSTANTunde_punde_a~=?z_hct)"
            show FALSE
            by (rule zenon_L4_ [OF z_Hcl z_Hee z_Hdc z_Hdd])
           qed
           have z_Hjo: "(?z_hdr~=?z_hdr)"
           by (rule subst [where P="(\<lambda>zenon_Veq. ((a_VARIABLEunde_pcunde_hash_primea[zenon_Veq])~=?z_hdr))", OF z_Hiv], fact z_Hjn)
           thus "(?z_hdr~=?z_hdr)" .
          qed
         qed
         have z_Hhi: "?z_hhi"
         by (rule subst [where P="(\<lambda>zenon_Vdq. (zenon_Vdq \\in {?z_hbd, ?z_hbe}))", OF z_Hjm], fact z_Hex)
         thus "?z_hhi" .
        qed
       qed
      qed
     qed
    next
     assume z_Hfq:"(?z_hch=''e'')" (is "_=?z_hbh")
     assume z_Hjt:"(?z_hbf=cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ?z_hbf))" (is "_=?z_hfr")
     have z_Him: "(?z_hbh~=?z_hbd)"
     by auto
     have z_Hdz: "(?z_hch~=?z_hch)"
     by (rule zenon_stringdiffll [OF z_Him z_Hfq z_He])
      show FALSE
      by (rule zenon_noteq [OF z_Hdz])
    next
     assume z_Hef:"((?z_hch~=''e'')&((~(?z_hch \\in {?z_hbd, ?z_hbe}))&((~(?z_hch \\in {''a'', ''b''}))&TRUE)))" (is "?z_heg&?z_heh")
     show FALSE
     by (rule zenon_L5_ [OF z_Hef z_He])
    qed
   qed
  next
   assume z_Hey:"(?z_hci=''e'')" (is "_=?z_hbh")
   assume z_Hju:"(cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B'')=?z_hck)" (is "?z_hez=_")
   have z_Hjf: "(?z_hbh~=?z_hbe)"
   by auto
   have z_Hds: "(?z_hci~=?z_hci)"
   by (rule zenon_stringdiffll [OF z_Hjf z_Hey z_Hf])
    show FALSE
    by (rule zenon_noteq [OF z_Hds])
  next
   assume z_Hjv:"((?z_hci~=''e'')&((~(?z_hci \\in {?z_hbd, ?z_hbe}))&((~(?z_hci \\in {''a'', ''b''}))&TRUE)))" (is "?z_hjw&?z_hjx")
   have z_Hjx: "?z_hjx" (is "?z_hjy&?z_hjz")
   by (rule zenon_and_1 [OF z_Hjv])
   have z_Hjy: "?z_hjy" (is "~?z_hex")
   by (rule zenon_and_0 [OF z_Hjx])
   have z_Hkb: "(~(?z_hci \\in {?z_hbe}))" (is "~?z_hkc")
   by (rule zenon_notin_addElt_1 [of "?z_hci" "?z_hbd" "{?z_hbe}", OF z_Hjy])
   have z_Hkd: "(?z_hci~=?z_hbe)"
   by (rule zenon_notin_addElt_0 [of "?z_hci" "?z_hbe" "{}", OF z_Hkb])
   show FALSE
   by (rule notE [OF z_Hkd z_Hf])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1574"; *} qed
lemma ob'1581:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'86: "((a_ACTIONunde_cunde_a ((a_CONSTANTunde_punde_a))))"
assumes v'101: "(((fapply ((a_STATEunde_pcBarunde_a), (a_CONSTANTunde_punde_a))) = (''B'')))"
assumes v'102: "(\<exists> a_CONSTANTunde_Vunde_a \<in> (subsetOf(((SUBSET ((a_CONSTANTunde_Sexcl_PUnionunde_a ((a_VARIABLEunde_myValsunde_a)))))), %a_CONSTANTunde_Wunde_a. ((((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (a_CONSTANTunde_Wunde_a))) & ((((a_CONSTANTunde_Sexcl_PUnionunde_a ((a_VARIABLEunde_nextoutunde_a)))) \<subseteq> (a_CONSTANTunde_Wunde_a)))))) : ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (a_CONSTANTunde_Vunde_a)]))))"
assumes v'103: "((((a_h8b086a :: c)) = ([(a_STATEunde_pcBarunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''C'')])))"
assumes v'104: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'105: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
shows "((((fapply ((a_STATEunde_pcBarunde_a), (a_CONSTANTunde_punde_a))) = (''B''))) & (\<exists> a_CONSTANTunde_Vunde_a \<in> (subsetOf(((SUBSET ((a_CONSTANTunde_Sexcl_PUnionunde_a ((a_VARIABLEunde_myValsunde_a)))))), %a_CONSTANTunde_Wunde_a. ((((fapply ((a_VARIABLEunde_myValsunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> (a_CONSTANTunde_Wunde_a))) & ((((a_CONSTANTunde_Sexcl_PUnionunde_a ((a_VARIABLEunde_nextoutunde_a)))) \<subseteq> (a_CONSTANTunde_Wunde_a)))))) : ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (a_CONSTANTunde_Vunde_a)])))) & ((((a_h8b086a :: c)) = ([(a_STATEunde_pcBarunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''C'')]))) & (((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'1581")
proof -
ML_command {* writeln "*** TLAPS ENTER 1581"; *}
show "PROP ?ob'1581"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_d4ff59.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_d4ff59.znn.out
;; obligation #1581
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'86" (a_ACTIONunde_cunde_a a_CONSTANTunde_punde_a)
$hyp "v'101" (= (TLA.fapply a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a)
"B")
$hyp "v'102" (TLA.bEx (TLA.subsetOf (TLA.SUBSET (a_CONSTANTunde_Sexcl_PUnionunde_a a_VARIABLEunde_myValsunde_a)) ((a_CONSTANTunde_Wunde_a) (/\ (TLA.subseteq (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
a_CONSTANTunde_Wunde_a)
(TLA.subseteq (a_CONSTANTunde_Sexcl_PUnionunde_a a_VARIABLEunde_nextoutunde_a)
a_CONSTANTunde_Wunde_a)))) ((a_CONSTANTunde_Vunde_a) (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a a_CONSTANTunde_Vunde_a))))
$hyp "v'103" (= a_h8b086a
(TLA.except a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a "C"))
$hyp "v'104" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'105" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$goal (/\ (= (TLA.fapply a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a) "B")
(TLA.bEx (TLA.subsetOf (TLA.SUBSET (a_CONSTANTunde_Sexcl_PUnionunde_a a_VARIABLEunde_myValsunde_a)) ((a_CONSTANTunde_Wunde_a) (/\ (TLA.subseteq (TLA.fapply a_VARIABLEunde_myValsunde_a a_CONSTANTunde_punde_a)
a_CONSTANTunde_Wunde_a)
(TLA.subseteq (a_CONSTANTunde_Sexcl_PUnionunde_a a_VARIABLEunde_nextoutunde_a)
a_CONSTANTunde_Wunde_a)))) ((a_CONSTANTunde_Vunde_a) (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a a_CONSTANTunde_Vunde_a))))
(= a_h8b086a (TLA.except a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a "C"))
(/\ (= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_STATEunde_pcBarunde_a[a_CONSTANTunde_punde_a])=''B'')" (is "?z_hk=?z_hn")
 using v'101 by blast
 have z_Hf:"bEx(subsetOf(SUBSET(a_CONSTANTunde_Sexcl_PUnionunde_a(a_VARIABLEunde_myValsunde_a)), (\<lambda>a_CONSTANTunde_Wunde_a. (((a_VARIABLEunde_myValsunde_a[a_CONSTANTunde_punde_a]) \\subseteq a_CONSTANTunde_Wunde_a)&(a_CONSTANTunde_Sexcl_PUnionunde_a(a_VARIABLEunde_nextoutunde_a) \\subseteq a_CONSTANTunde_Wunde_a)))), (\<lambda>a_CONSTANTunde_Vunde_a. (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, a_CONSTANTunde_Vunde_a))))" (is "?z_hf")
 using v'102 by blast
 have z_Hg:"(a_h8b086a=except(a_STATEunde_pcBarunde_a, a_CONSTANTunde_punde_a, ''C''))" (is "_=?z_hbg")
 using v'103 by blast
 have z_Hh:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'104 by blast
 have z_Hi:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'105 by blast
 assume z_Hj:"(~((?z_hk=?z_hn)&(?z_hf&((a_h8b086a=?z_hbg)&((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a))))))" (is "~(?z_he&?z_hbm)")
 show FALSE
 proof (rule zenon_notand [OF z_Hj])
  assume z_Hbp:"(?z_hk~=?z_hn)"
  show FALSE
  by (rule notE [OF z_Hbp z_He])
 next
  assume z_Hbq:"(~?z_hbm)" (is "~(_&?z_hbn)")
  show FALSE
  proof (rule zenon_notand [OF z_Hbq])
   assume z_Hbr:"(~?z_hf)"
   show FALSE
   by (rule notE [OF z_Hbr z_Hf])
  next
   assume z_Hbs:"(~?z_hbn)" (is "~(?z_hg&?z_hbo)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbs])
    assume z_Hbt:"(a_h8b086a~=?z_hbg)"
    show FALSE
    by (rule notE [OF z_Hbt z_Hg])
   next
    assume z_Hbu:"(~?z_hbo)" (is "~(?z_hh&?z_hi)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbu])
     assume z_Hbv:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
     show FALSE
     by (rule notE [OF z_Hbv z_Hh])
    next
     assume z_Hbw:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
     show FALSE
     by (rule notE [OF z_Hbw z_Hi])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1581"; *} qed
lemma ob'1587:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'75: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'76: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'79: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'87: "((a_ACTIONunde_cunde_a ((a_CONSTANTunde_punde_a))))"
assumes v'106: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'107: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'108: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'109: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'110: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
assumes v'111: "(((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))"
assumes v'112: "((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))"
assumes v'113: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')])))"
assumes v'114: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'115: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'116: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'117: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'118: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'119: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
shows "((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c''))) & ((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({}))) & (((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))) & (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) & ((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a))) & ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a))) & ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'1587")
proof -
ML_command {* writeln "*** TLAPS ENTER 1587"; *}
show "PROP ?ob'1587"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_959354.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_959354.znn.out
;; obligation #1587
$hyp "v'75" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'76" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'79" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'87" (a_ACTIONunde_cunde_a a_CONSTANTunde_punde_a)
$hyp "v'106" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'107" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'108" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'109" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'110" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$hyp "v'111" (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a)))
$hyp "v'112" (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
$hyp "v'113" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))
$hyp "v'114" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'115" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'116" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'117" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'118" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'119" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$goal (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "c")
(= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
(= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a)))
(= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))
(/\ (= a_VARIABLEunde_resultunde_hash_primea a_VARIABLEunde_resultunde_a)
(= a_VARIABLEunde_A2unde_hash_primea a_VARIABLEunde_A2unde_a)
(= a_VARIABLEunde_A3unde_hash_primea a_VARIABLEunde_A3unde_a)
(= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_nbpartunde_hash_primea a_VARIABLEunde_nbpartunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''c'')" (is "?z_ht=?z_hw")
 using v'106 by blast
 have z_Hf:"(a_VARIABLEunde_lnbpartunde_hash_primea=except(a_VARIABLEunde_lnbpartunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])))" (is "_=?z_hy")
 using v'107 by blast
 have z_Hg:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hbd")
 using v'108 by blast
 have z_Hh:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, ((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]) +  -.(1))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hbp")
 using v'109 by blast
 have z_Hi:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})" (is "?z_hca=_")
 using v'110 by blast
 have z_Hj:"((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a)))" (is "?z_hba=?z_hcc")
 using v'111 by blast
 have z_Hk:"(a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_=?z_hcg")
 using v'112 by blast
 have z_Hl:"(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))" (is "_=?z_hcj")
 using v'113 by blast
 have z_Hm:"(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)"
 using v'114 by blast
 have z_Hn:"(a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)"
 using v'115 by blast
 have z_Ho:"(a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)"
 using v'116 by blast
 have z_Hp:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'117 by blast
 have z_Hq:"(a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)"
 using v'118 by blast
 have z_Hr:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'119 by blast
 assume z_Hs:"(~((?z_ht=?z_hw)&((a_VARIABLEunde_lnbpartunde_hash_primea=?z_hy)&((a_VARIABLEunde_knownunde_hash_primea=?z_hbd)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbp)&((?z_hca={})&((?z_hba=?z_hcc)&((a_VARIABLEunde_nextoutunde_hash_primea=?z_hcg)&((a_VARIABLEunde_pcunde_hash_primea=?z_hcj)&((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)&((a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)&((a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)&((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&((a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)))))))))))))))" (is "~(?z_he&?z_hcv)")
 show FALSE
 proof (rule zenon_notand [OF z_Hs])
  assume z_Hdh:"(?z_ht~=?z_hw)"
  show FALSE
  by (rule notE [OF z_Hdh z_He])
 next
  assume z_Hdi:"(~?z_hcv)" (is "~(?z_hf&?z_hcw)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdi])
   assume z_Hdj:"(a_VARIABLEunde_lnbpartunde_hash_primea~=?z_hy)"
   show FALSE
   by (rule notE [OF z_Hdj z_Hf])
  next
   assume z_Hdk:"(~?z_hcw)" (is "~(?z_hg&?z_hcx)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdk])
    assume z_Hdl:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbd)"
    show FALSE
    by (rule notE [OF z_Hdl z_Hg])
   next
    assume z_Hdm:"(~?z_hcx)" (is "~(?z_hh&?z_hcy)")
    show FALSE
    proof (rule zenon_notand [OF z_Hdm])
     assume z_Hdn:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbp)"
     show FALSE
     by (rule notE [OF z_Hdn z_Hh])
    next
     assume z_Hdo:"(~?z_hcy)" (is "~(?z_hi&?z_hcz)")
     show FALSE
     proof (rule zenon_notand [OF z_Hdo])
      assume z_Hdp:"(?z_hca~={})"
      show FALSE
      by (rule notE [OF z_Hdp z_Hi])
     next
      assume z_Hdq:"(~?z_hcz)" (is "~(?z_hj&?z_hda)")
      show FALSE
      proof (rule zenon_notand [OF z_Hdq])
       assume z_Hdr:"(?z_hba~=?z_hcc)"
       show FALSE
       by (rule notE [OF z_Hdr z_Hj])
      next
       assume z_Hds:"(~?z_hda)" (is "~(?z_hk&?z_hdb)")
       show FALSE
       proof (rule zenon_notand [OF z_Hds])
        assume z_Hdt:"(a_VARIABLEunde_nextoutunde_hash_primea~=?z_hcg)"
        show FALSE
        by (rule notE [OF z_Hdt z_Hk])
       next
        assume z_Hdu:"(~?z_hdb)" (is "~(?z_hl&?z_hdc)")
        show FALSE
        proof (rule zenon_notand [OF z_Hdu])
         assume z_Hdv:"(a_VARIABLEunde_pcunde_hash_primea~=?z_hcj)"
         show FALSE
         by (rule notE [OF z_Hdv z_Hl])
        next
         assume z_Hdw:"(~?z_hdc)" (is "~(?z_hm&?z_hdd)")
         show FALSE
         proof (rule zenon_notand [OF z_Hdw])
          assume z_Hdx:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
          show FALSE
          by (rule notE [OF z_Hdx z_Hm])
         next
          assume z_Hdy:"(~?z_hdd)" (is "~(?z_hn&?z_hde)")
          show FALSE
          proof (rule zenon_notand [OF z_Hdy])
           assume z_Hdz:"(a_VARIABLEunde_A2unde_hash_primea~=a_VARIABLEunde_A2unde_a)"
           show FALSE
           by (rule notE [OF z_Hdz z_Hn])
          next
           assume z_Hea:"(~?z_hde)" (is "~(?z_ho&?z_hdf)")
           show FALSE
           proof (rule zenon_notand [OF z_Hea])
            assume z_Heb:"(a_VARIABLEunde_A3unde_hash_primea~=a_VARIABLEunde_A3unde_a)"
            show FALSE
            by (rule notE [OF z_Heb z_Ho])
           next
            assume z_Hec:"(~?z_hdf)" (is "~(?z_hp&?z_hdg)")
            show FALSE
            proof (rule zenon_notand [OF z_Hec])
             assume z_Hed:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
             show FALSE
             by (rule notE [OF z_Hed z_Hp])
            next
             assume z_Hee:"(~?z_hdg)" (is "~(?z_hq&?z_hr)")
             show FALSE
             proof (rule zenon_notand [OF z_Hee])
              assume z_Hef:"(a_VARIABLEunde_nbpartunde_hash_primea~=a_VARIABLEunde_nbpartunde_a)"
              show FALSE
              by (rule notE [OF z_Hef z_Hq])
             next
              assume z_Heg:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
              show FALSE
              by (rule notE [OF z_Heg z_Hr])
             qed
            qed
           qed
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1587"; *} qed
lemma ob'1605:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'86: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'87: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'88: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'89: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A3unde_a))))))])))"
assumes v'90: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'91: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'92: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'93: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'94: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'95: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'96: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
assumes v'112: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
assumes v'113: "(((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))"
shows "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"(is "PROP ?ob'1605")
proof -
ML_command {* writeln "*** TLAPS ENTER 1605"; *}
show "PROP ?ob'1605"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_e9c1cb.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_e9c1cb.znn.out
;; obligation #1605
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'86" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'87" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'88" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'89" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A3unde_a))))
$hyp "v'90" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'91" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'92" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'93" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'94" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'95" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'96" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "v'112" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$hyp "v'113" (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a)))
$goal (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ho:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})" (is "?z_hr=_")
 using v'112 by blast
 assume z_Hq:"(?z_hr~={})"
 show FALSE
 by (rule notE [OF z_Hq z_Ho])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1605"; *} qed
lemma ob'1609:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'86: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'87: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'88: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'89: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A3unde_a))))))])))"
assumes v'90: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'91: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'92: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'93: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'94: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'95: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'96: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
assumes v'114: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
assumes v'115: "(((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))"
shows "((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))"(is "PROP ?ob'1609")
proof -
ML_command {* writeln "*** TLAPS ENTER 1609"; *}
show "PROP ?ob'1609"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_7954aa.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_7954aa.znn.out
;; obligation #1609
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'86" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'87" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'88" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'89" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A3unde_a))))
$hyp "v'90" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'91" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'92" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'93" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'94" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'95" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'96" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "v'114" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$hyp "v'115" (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a)))
$goal (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)), (cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))))" (is "?z_hd")
 using v'86 by blast
 have z_Hp:"((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a)))" (is "?z_hbh=?z_hbj")
 using v'115 by blast
 have z_Ho:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})" (is "?z_hs=_")
 using v'114 by blast
 assume z_Hq:"(a_VARIABLEunde_nextoutunde_hash_primea~=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hbn")
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hs~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" "(cond((?z_hbh=?z_hbj), (a_VARIABLEunde_nextoutunde_hash_primea=?z_hbn), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
  assume z_Hr:"(?z_hs~={})"
  assume z_Hw:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "?z_hx&?z_hbc")
  show FALSE
  by (rule notE [OF z_Hr z_Ho])
 next
  assume z_Hbx:"(~(?z_hs~={}))" (is "~~?z_ho")
  assume z_Hbf:"(cond((?z_hbh=?z_hbj), (a_VARIABLEunde_nextoutunde_hash_primea=?z_hbn), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hbg&?z_hbs")
  have z_Hbg: "?z_hbg"
  by (rule zenon_and_0 [OF z_Hbf])
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hbh=?z_hbj)" "(a_VARIABLEunde_nextoutunde_hash_primea=?z_hbn)" "(TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))", OF z_Hbg])
   assume z_Hp:"(?z_hbh=?z_hbj)"
   assume z_Hbm:"(a_VARIABLEunde_nextoutunde_hash_primea=?z_hbn)"
   show FALSE
   by (rule notE [OF z_Hq z_Hbm])
  next
   assume z_Hby:"(?z_hbh~=?z_hbj)"
   assume z_Hbq:"(TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "?z_hbr&?z_hbc")
   show FALSE
   by (rule notE [OF z_Hby z_Hp])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1609"; *} qed
lemma ob'1611:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'86: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'87: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'88: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'89: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A3unde_a))))))])))"
assumes v'90: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'91: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'92: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'93: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'94: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'95: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'96: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
assumes v'115: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
assumes v'116: "(((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a)))))))))"
shows "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')])))"(is "PROP ?ob'1611")
proof -
ML_command {* writeln "*** TLAPS ENTER 1611"; *}
show "PROP ?ob'1611"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_906194.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_906194.znn.out
;; obligation #1611
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'86" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'87" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'88" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'89" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A3unde_a))))
$hyp "v'90" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'91" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'92" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'93" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'94" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'95" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'96" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "v'115" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$hyp "v'116" (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a)))
$goal (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)), (cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))))" (is "?z_hd")
 using v'86 by blast
 have z_Ho:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})" (is "?z_hs=_")
 using v'115 by blast
 assume z_Hq:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))" (is "_~=?z_hbt")
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hs~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" "(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=?z_hbt))", OF z_Hd])
  assume z_Hr:"(?z_hs~={})"
  assume z_Hw:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a))" (is "?z_hx&?z_hbc")
  show FALSE
  by (rule notE [OF z_Hr z_Ho])
 next
  assume z_Hbx:"(~(?z_hs~={}))" (is "~~?z_ho")
  assume z_Hbf:"(cond(((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=?z_hbt))" (is "?z_hbg&?z_hbs")
  have z_Hbs: "?z_hbs"
  by (rule zenon_and_1 [OF z_Hbf])
  show FALSE
  by (rule notE [OF z_Hq z_Hbs])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1611"; *} qed
lemma ob'1679:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'73: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'74: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'77: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'85: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''d'')]))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))), ((cond((((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) = ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))), (((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = ([(a_VARIABLEunde_nextoutunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))), ((TRUE) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a)))))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))))))"
assumes v'86: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'87: "((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))])))"
assumes v'88: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'89: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'90: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'91: "((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a)))"
assumes v'92: "((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a)))"
assumes v'93: "((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a)))"
assumes v'94: "((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a)))"
assumes v'95: "((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))"
assumes v'106: "(((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a))))))))))))"
assumes v'107: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
shows "((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c''))) & ((((a_VARIABLEunde_lnbpartunde_hash_primea :: c)) = ([(a_VARIABLEunde_lnbpartunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((arith_add ((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))), ((minus (((Succ[0]))))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A3unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({}))) & (((fapply ((a_VARIABLEunde_nbpartunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A2unde_a), (a_CONSTANTunde_iunde_a)))))))))))) & ((((a_VARIABLEunde_nextoutunde_hash_primea :: c)) = (a_VARIABLEunde_nextoutunde_a))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''e'')]))) & (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) & ((((a_VARIABLEunde_A2unde_hash_primea :: c)) = (a_VARIABLEunde_A2unde_a))) & ((((a_VARIABLEunde_A3unde_hash_primea :: c)) = (a_VARIABLEunde_A3unde_a))) & ((((a_VARIABLEunde_myValsunde_hash_primea :: c)) = (a_VARIABLEunde_myValsunde_a))) & ((((a_VARIABLEunde_nbpartunde_hash_primea :: c)) = (a_VARIABLEunde_nbpartunde_a))) & ((((a_VARIABLEunde_outunde_hash_primea :: c)) = (a_VARIABLEunde_outunde_a)))))"(is "PROP ?ob'1679")
proof -
ML_command {* writeln "*** TLAPS ENTER 1679"; *}
show "PROP ?ob'1679"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_45845d.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_45845d.znn.out
;; obligation #1679
$hyp "v'73" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'74" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'77" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'85" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "d"))
(= a_VARIABLEunde_nextoutunde_hash_primea
a_VARIABLEunde_nextoutunde_a)) (/\ (TLA.cond (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))) (/\ (= a_VARIABLEunde_nextoutunde_hash_primea
(TLA.except a_VARIABLEunde_nextoutunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))) (/\ T.
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))))
$hyp "v'86" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'87" (= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
$hyp "v'88" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'89" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'90" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'91" (= a_VARIABLEunde_A2unde_hash_primea
a_VARIABLEunde_A2unde_a)
$hyp "v'92" (= a_VARIABLEunde_A3unde_hash_primea
a_VARIABLEunde_A3unde_a)
$hyp "v'93" (= a_VARIABLEunde_myValsunde_hash_primea
a_VARIABLEunde_myValsunde_a)
$hyp "v'94" (= a_VARIABLEunde_nbpartunde_hash_primea
a_VARIABLEunde_nbpartunde_a)
$hyp "v'95" (= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)
$hyp "v'106" (-. (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'107" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$goal (/\ (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a) "c")
(= a_VARIABLEunde_lnbpartunde_hash_primea
(TLA.except a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(arith.add (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A3unde_a a_CONSTANTunde_iunde_a)))))))
(= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
(-. (= (TLA.fapply a_VARIABLEunde_nbpartunde_a a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A2unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_nextoutunde_hash_primea a_VARIABLEunde_nextoutunde_a)
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "e"))
(/\ (= a_VARIABLEunde_resultunde_hash_primea a_VARIABLEunde_resultunde_a)
(= a_VARIABLEunde_A2unde_hash_primea a_VARIABLEunde_A2unde_a)
(= a_VARIABLEunde_A3unde_hash_primea a_VARIABLEunde_A3unde_a)
(= a_VARIABLEunde_myValsunde_hash_primea a_VARIABLEunde_myValsunde_a)
(= a_VARIABLEunde_nbpartunde_hash_primea a_VARIABLEunde_nbpartunde_a)
(= a_VARIABLEunde_outunde_hash_primea
a_VARIABLEunde_outunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''c'')" (is "?z_hr=?z_hu")
 using v'86 by blast
 have z_Hf:"(a_VARIABLEunde_lnbpartunde_hash_primea=except(a_VARIABLEunde_lnbpartunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])))" (is "_=?z_hw")
 using v'87 by blast
 have z_Hg:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hbb")
 using v'88 by blast
 have z_Hh:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, ((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a]) +  -.(1))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A3unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hbn")
 using v'89 by blast
 have z_Ho:"((a_VARIABLEunde_nbpartunde_a[a_CONSTANTunde_punde_a])~=a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A2unde_a[a_CONSTANTunde_iunde_a]))))))" (is "?z_hy~=?z_hby")
 using v'106 by blast
 have z_Hp:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})" (is "?z_hce=_")
 using v'107 by blast
 have z_Hd:"cond((?z_hce~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)), (cond((?z_hy=?z_hby), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&(a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))))" (is "?z_hd")
 using v'85 by blast
 have z_Hi:"(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)"
 using v'90 by blast
 have z_Hj:"(a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)"
 using v'91 by blast
 have z_Hk:"(a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)"
 using v'92 by blast
 have z_Hl:"(a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)"
 using v'93 by blast
 have z_Hm:"(a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)"
 using v'94 by blast
 have z_Hn:"(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)"
 using v'95 by blast
 assume z_Hq:"(~((?z_hr=?z_hu)&((a_VARIABLEunde_lnbpartunde_hash_primea=?z_hw)&((a_VARIABLEunde_knownunde_hash_primea=?z_hbb)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbn)&((?z_hce={})&((?z_hy~=?z_hby)&((a_VARIABLEunde_nextoutunde_hash_primea=a_VARIABLEunde_nextoutunde_a)&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))&((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)&((a_VARIABLEunde_A2unde_hash_primea=a_VARIABLEunde_A2unde_a)&((a_VARIABLEunde_A3unde_hash_primea=a_VARIABLEunde_A3unde_a)&((a_VARIABLEunde_myValsunde_hash_primea=a_VARIABLEunde_myValsunde_a)&((a_VARIABLEunde_nbpartunde_hash_primea=a_VARIABLEunde_nbpartunde_a)&(a_VARIABLEunde_outunde_hash_primea=a_VARIABLEunde_outunde_a)))))))))))))))" (is "~(?z_he&?z_hdj)")
 show FALSE
 proof (rule zenon_notand [OF z_Hq])
  assume z_Hdv:"(?z_hr~=?z_hu)"
  show FALSE
  by (rule notE [OF z_Hdv z_He])
 next
  assume z_Hdw:"(~?z_hdj)" (is "~(?z_hf&?z_hdk)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdw])
   assume z_Hdx:"(a_VARIABLEunde_lnbpartunde_hash_primea~=?z_hw)"
   show FALSE
   by (rule notE [OF z_Hdx z_Hf])
  next
   assume z_Hdy:"(~?z_hdk)" (is "~(?z_hg&?z_hdl)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdy])
    assume z_Hdz:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbb)"
    show FALSE
    by (rule notE [OF z_Hdz z_Hg])
   next
    assume z_Hea:"(~?z_hdl)" (is "~(?z_hh&?z_hdm)")
    show FALSE
    proof (rule zenon_notand [OF z_Hea])
     assume z_Heb:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbn)"
     show FALSE
     by (rule notE [OF z_Heb z_Hh])
    next
     assume z_Hec:"(~?z_hdm)" (is "~(?z_hp&?z_hdn)")
     show FALSE
     proof (rule zenon_notand [OF z_Hec])
      assume z_Hcg:"(?z_hce~={})"
      show FALSE
      by (rule notE [OF z_Hcg z_Hp])
     next
      assume z_Hed:"(~?z_hdn)" (is "~(?z_ho&?z_hdo)")
      show FALSE
      proof (rule zenon_notand [OF z_Hed])
       assume z_Hee:"(~?z_ho)" (is "~~?z_hcr")
       show FALSE
       by (rule notE [OF z_Hee z_Ho])
      next
       assume z_Hef:"(~?z_hdo)" (is "~(?z_hcm&?z_hdp)")
       show FALSE
       proof (rule zenon_notand [OF z_Hef])
        assume z_Heg:"(a_VARIABLEunde_nextoutunde_hash_primea~=a_VARIABLEunde_nextoutunde_a)"
        show FALSE
        proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hce~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hcm)" "(cond((?z_hy=?z_hby), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hcm))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))", OF z_Hd])
         assume z_Hcg:"(?z_hce~={})"
         assume z_Hch:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hcm)" (is "?z_hci&_")
         show FALSE
         by (rule notE [OF z_Hcg z_Hp])
        next
         assume z_Hej:"(~(?z_hce~={}))"
         assume z_Hcp:"(cond((?z_hy=?z_hby), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hcm))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e'')))" (is "?z_hcq&?z_hcw")
         have z_Hcq: "?z_hcq"
         by (rule zenon_and_0 [OF z_Hcp])
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hy=?z_hby)" "(a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" "(TRUE&?z_hcm)", OF z_Hcq])
          assume z_Hcr:"(?z_hy=?z_hby)"
          assume z_Hcs:"(a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_=?z_hct")
          show FALSE
          by (rule notE [OF z_Ho z_Hcr])
         next
          assume z_Ho:"?z_ho"
          assume z_Hcu:"(TRUE&?z_hcm)" (is "?z_hcv&_")
          have z_Hcm: "?z_hcm"
          by (rule zenon_and_1 [OF z_Hcu])
          show FALSE
          by (rule notE [OF z_Heg z_Hcm])
         qed
        qed
       next
        assume z_Hek:"(~?z_hdp)" (is "~(?z_hcw&?z_hdq)")
        show FALSE
        proof (rule zenon_notand [OF z_Hek])
         assume z_Hel:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''e''))" (is "_~=?z_hcx")
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hce~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hcm)" "(cond((?z_hy=?z_hby), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hcm))&?z_hcw)", OF z_Hd])
          assume z_Hcg:"(?z_hce~={})"
          assume z_Hch:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''d''))&?z_hcm)" (is "?z_hci&_")
          show FALSE
          by (rule notE [OF z_Hcg z_Hp])
         next
          assume z_Hej:"(~(?z_hce~={}))"
          assume z_Hcp:"(cond((?z_hy=?z_hby), (a_VARIABLEunde_nextoutunde_hash_primea=except(a_VARIABLEunde_nextoutunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (TRUE&?z_hcm))&?z_hcw)" (is "?z_hcq&_")
          have z_Hcw: "?z_hcw"
          by (rule zenon_and_1 [OF z_Hcp])
          show FALSE
          by (rule notE [OF z_Hel z_Hcw])
         qed
        next
         assume z_Hem:"(~?z_hdq)" (is "~(?z_hi&?z_hdr)")
         show FALSE
         proof (rule zenon_notand [OF z_Hem])
          assume z_Hen:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
          show FALSE
          by (rule notE [OF z_Hen z_Hi])
         next
          assume z_Heo:"(~?z_hdr)" (is "~(?z_hj&?z_hds)")
          show FALSE
          proof (rule zenon_notand [OF z_Heo])
           assume z_Hep:"(a_VARIABLEunde_A2unde_hash_primea~=a_VARIABLEunde_A2unde_a)"
           show FALSE
           by (rule notE [OF z_Hep z_Hj])
          next
           assume z_Heq:"(~?z_hds)" (is "~(?z_hk&?z_hdt)")
           show FALSE
           proof (rule zenon_notand [OF z_Heq])
            assume z_Her:"(a_VARIABLEunde_A3unde_hash_primea~=a_VARIABLEunde_A3unde_a)"
            show FALSE
            by (rule notE [OF z_Her z_Hk])
           next
            assume z_Hes:"(~?z_hdt)" (is "~(?z_hl&?z_hdu)")
            show FALSE
            proof (rule zenon_notand [OF z_Hes])
             assume z_Het:"(a_VARIABLEunde_myValsunde_hash_primea~=a_VARIABLEunde_myValsunde_a)"
             show FALSE
             by (rule notE [OF z_Het z_Hl])
            next
             assume z_Heu:"(~?z_hdu)" (is "~(?z_hm&?z_hn)")
             show FALSE
             proof (rule zenon_notand [OF z_Heu])
              assume z_Hev:"(a_VARIABLEunde_nbpartunde_hash_primea~=a_VARIABLEunde_nbpartunde_a)"
              show FALSE
              by (rule notE [OF z_Hev z_Hm])
             next
              assume z_Hew:"(a_VARIABLEunde_outunde_hash_primea~=a_VARIABLEunde_outunde_a)"
              show FALSE
              by (rule notE [OF z_Hew z_Hn])
             qed
            qed
           qed
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1679"; *} qed
lemma ob'1683:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_CONSTANTunde_Valunde_a
(* usable definition CONSTANT_NUnion_ suppressed *)
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_A2unde_a a_VARIABLEunde_A2unde_a'
fixes a_VARIABLEunde_A3unde_a a_VARIABLEunde_A3unde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_myValsunde_a a_VARIABLEunde_myValsunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
fixes a_VARIABLEunde_lnbpartunde_a a_VARIABLEunde_lnbpartunde_a'
fixes a_VARIABLEunde_nbpartunde_a a_VARIABLEunde_nbpartunde_a'
fixes a_VARIABLEunde_nextoutunde_a a_VARIABLEunde_nextoutunde_a'
fixes a_VARIABLEunde_outunde_a a_VARIABLEunde_outunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_c_ suppressed *)
(* usable definition ACTION_d_ suppressed *)
(* usable definition ACTION_e_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_PUnion_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Inv1_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA3_ suppressed *)
(* usable definition STATE_Inv2_ suppressed *)
(* usable definition CONSTANT_S!PUnion_ suppressed *)
(* usable definition STATE_S!vars_ suppressed *)
(* usable definition STATE_S!Init_ suppressed *)
(* usable definition ACTION_S!A_ suppressed *)
(* usable definition ACTION_S!B_ suppressed *)
(* usable definition ACTION_S!C_ suppressed *)
(* usable definition ACTION_S!Next_ suppressed *)
(* usable definition TEMPORAL_S!Spec_ suppressed *)
(* usable definition STATE_S!TypeOK_ suppressed *)
(* usable definition ACTION_S!BigNext_ suppressed *)
(* usable definition TEMPORAL_S!BigSpec_ suppressed *)
assumes v'74: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
assumes v'75: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
assumes v'78: "(((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_Inv1unde_a))) \<and> (a_STATEunde_Inv2unde_a)))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'86: "((a_ACTIONunde_cunde_a ((a_CONSTANTunde_punde_a))))"
assumes v'99: "(((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c))))))))))"
assumes v'100: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''c'')))"
assumes v'101: "(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (''e'')))"
assumes v'102: "(((fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_punde_a))) = (fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_punde_a)))))"
assumes v'103: "(\<forall> a_CONSTANTunde_qunde_a \<in> (((a_CONSTANTunde_Procunde_a) \\ ({(a_CONSTANTunde_punde_a)}))) : (((fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_qunde_a))) = (fapply (([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))]), (a_CONSTANTunde_qunde_a))))))"
shows "((([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply (((a_VARIABLEunde_lnbpartunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a (((a_VARIABLEunde_A2unde_hash_primea :: c)))))))))), (''C''), (''B'')))>>))]) = ([ a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a)  \<mapsto> (Case(<<(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''a''), (''b'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) \<in> ({(''c''), (''d'')}))), (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a_1))) = (''e'')))>>,<<(''A''), (''B''), (cond((((fapply ((a_VARIABLEunde_lnbpartunde_a), (a_CONSTANTunde_punde_a_1))) = ((a_CONSTANTunde_Cardinalityunde_a (((a_CONSTANTunde_NUnionunde_a ((a_VARIABLEunde_A2unde_a))))))))), (''C''), (''B'')))>>))])))"(is "PROP ?ob'1683")
proof -
ML_command {* writeln "*** TLAPS ENTER 1683"; *}
show "PROP ?ob'1683"

(* BEGIN ZENON INPUT
;; file=.tlacache/SnapShot_test.tlaps/tlapm_f915d3.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/SnapShot_test.tlaps/tlapm_f915d3.znn.out
;; obligation #1683
$hyp "v'74" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "v'75" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "v'78" (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_Inv1unde_a)
a_STATEunde_Inv2unde_a)
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'86" (a_ACTIONunde_cunde_a a_CONSTANTunde_punde_a)
$hyp "v'99" (-. (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))))
$hyp "v'100" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"c")
$hyp "v'101" (= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a)
"e")
$hyp "v'102" (= (TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") ))) a_CONSTANTunde_punde_a)
(TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))) a_CONSTANTunde_punde_a))
$hyp "v'103" (TLA.bAll (TLA.setminus a_CONSTANTunde_Procunde_a
(TLA.set a_CONSTANTunde_punde_a)) ((a_CONSTANTunde_qunde_a) (= (TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") ))) a_CONSTANTunde_qunde_a)
(TLA.fapply (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))) a_CONSTANTunde_qunde_a))))
$goal (= (TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_hash_primea a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_hash_primea))) "C" "B") )))
(TLA.Fcn a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.CASE (TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "a" "b")) "A"
(TLA.in (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
(TLA.set "c" "d")) "B"
(= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a_1)
"e") (TLA.cond (= (TLA.fapply a_VARIABLEunde_lnbpartunde_a a_CONSTANTunde_punde_a_1)
(a_CONSTANTunde_Cardinalityunde_a (a_CONSTANTunde_NUnionunde_a a_VARIABLEunde_A2unde_a))) "C" "B") ))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[a_CONSTANTunde_qunde_a])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[a_CONSTANTunde_qunde_a]))))" (is "?z_hi")
 using v'103 by blast
 have z_Hh:"((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[a_CONSTANTunde_punde_a])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[a_CONSTANTunde_punde_a]))" (is "?z_hci=?z_hcj")
 using v'102 by blast
 have zenon_L1_: "(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[x])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[x])))) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))~=a_CONSTANTunde_punde_a) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a) ==> ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])) ==> FALSE" (is "?z_hck ==> ?z_hcr ==> ?z_hdb ==> ?z_hdc ==> FALSE")
 proof -
  assume z_Hck:"?z_hck" (is "\\A x : ?z_hdf(x)")
  assume z_Hcr:"?z_hcr" (is "?z_hcs~=_")
  assume z_Hdb:"?z_hdb"
  assume z_Hdc:"?z_hdc" (is "?z_hdd~=?z_hde")
  have z_Hdg: "?z_hdf(?z_hcs)" (is "?z_hdh=>?z_hdi")
  by (rule zenon_all_0 [of "?z_hdf" "?z_hcs", OF z_Hck])
  show FALSE
  proof (rule zenon_imply [OF z_Hdg])
   assume z_Hdj:"(~?z_hdh)"
   show FALSE
   proof (rule zenon_notin_setminus [of "?z_hcs" "a_CONSTANTunde_Procunde_a" "{a_CONSTANTunde_punde_a}", OF z_Hdj])
    assume z_Hdk:"(~?z_hdb)"
    show FALSE
    by (rule notE [OF z_Hdk z_Hdb])
   next
    assume z_Hdl:"(?z_hcs \\in {a_CONSTANTunde_punde_a})" (is "?z_hdl")
    show FALSE
    proof (rule zenon_in_addElt [of "?z_hcs" "a_CONSTANTunde_punde_a" "{}", OF z_Hdl])
     assume z_Hdn:"(?z_hcs=a_CONSTANTunde_punde_a)"
     show FALSE
     by (rule notE [OF z_Hcr z_Hdn])
    next
     assume z_Hdo:"(?z_hcs \\in {})" (is "?z_hdo")
     show FALSE
     by (rule zenon_in_emptyset [of "?z_hcs", OF z_Hdo])
    qed
   qed
  next
   assume z_Hdi:"?z_hdi"
   show FALSE
   by (rule notE [OF z_Hdc z_Hdi])
  qed
 qed
 have zenon_L2_: "(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[x])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[x])))) ==> (a_CONSTANTunde_punde_a~=(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))) ==> ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a) ==> ((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])~=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))))=>((Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))[zenon_Vg])=(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B''))))[zenon_Vg])))))])) ==> FALSE" (is "?z_hck ==> ?z_hdp ==> ?z_hdb ==> ?z_hdc ==> FALSE")
 proof -
  assume z_Hck:"?z_hck" (is "\\A x : ?z_hdf(x)")
  assume z_Hdp:"?z_hdp" (is "_~=?z_hcs")
  assume z_Hdb:"?z_hdb"
  assume z_Hdc:"?z_hdc" (is "?z_hdd~=?z_hde")
  have z_Hdg: "?z_hdf(?z_hcs)" (is "?z_hdh=>?z_hdi")
  by (rule zenon_all_0 [of "?z_hdf" "?z_hcs", OF z_Hck])
  show FALSE
  proof (rule zenon_imply [OF z_Hdg])
   assume z_Hdj:"(~?z_hdh)"
   show FALSE
   proof (rule zenon_notin_setminus [of "?z_hcs" "a_CONSTANTunde_Procunde_a" "{a_CONSTANTunde_punde_a}", OF z_Hdj])
    assume z_Hdk:"(~?z_hdb)"
    show FALSE
    by (rule notE [OF z_Hdk z_Hdb])
   next
    assume z_Hdl:"(?z_hcs \\in {a_CONSTANTunde_punde_a})" (is "?z_hdl")
    show FALSE
    proof (rule zenon_in_addElt [of "?z_hcs" "a_CONSTANTunde_punde_a" "{}", OF z_Hdl])
     assume z_Hdn:"(?z_hcs=a_CONSTANTunde_punde_a)"
     show FALSE
     by (rule zenon_eqsym [OF z_Hdn z_Hdp])
    next
     assume z_Hdo:"(?z_hcs \\in {})" (is "?z_hdo")
     show FALSE
     by (rule zenon_in_emptyset [of "?z_hcs", OF z_Hdo])
    qed
   qed
  next
   assume z_Hdi:"?z_hdi"
   show FALSE
   by (rule notE [OF z_Hdc z_Hdi])
  qed
 qed
 assume z_Hj:"(Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B''))))~=Fcn(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))))" (is "?z_hr~=?z_hbt")
 have z_Hck_z_Hi: "(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((?z_hr[x])=(?z_hbt[x])))) == ?z_hi" (is "?z_hck == _")
 by (unfold bAll_def)
 have z_Hck: "?z_hck" (is "\\A x : ?z_hdf(x)")
 by (unfold z_Hck_z_Hi, fact z_Hi)
 have z_Hdq: "(~(((isAFcn(?z_hr)&isAFcn(?z_hbt))&(DOMAIN(?z_hr)=DOMAIN(?z_hbt)))&(\\A zenon_Vg:((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg]))))))" (is "~(?z_hds&?z_hdy)")
 by (rule zenon_notfunequal_0 [of "?z_hr" "?z_hbt", OF z_Hj])
 show FALSE
 proof (rule zenon_notand [OF z_Hdq])
  assume z_Hdz:"(~?z_hds)" (is "~(?z_hdt&?z_hdw)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdz])
   assume z_Hea:"(~?z_hdt)" (is "~(?z_hdu&?z_hdv)")
   show FALSE
   proof (rule zenon_notand [OF z_Hea])
    assume z_Heb:"(~?z_hdu)"
    show FALSE
    by (rule zenon_notisafcn_fcn [of "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B'')))", OF z_Heb])
   next
    assume z_Hec:"(~?z_hdv)"
    show FALSE
    by (rule zenon_notisafcn_fcn [of "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))", OF z_Hec])
   qed
  next
   assume z_Hed:"(DOMAIN(?z_hr)~=DOMAIN(?z_hbt))" (is "?z_hdx~=?z_hcx")
   have z_Hee: "(a_CONSTANTunde_Procunde_a~=?z_hcx)"
   by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vcr. (zenon_Vcr~=?z_hcx))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_hash_primea[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_hash_primea))), ''C'', ''B'')))", OF z_Hed])
   have z_Hei: "(a_CONSTANTunde_Procunde_a~=a_CONSTANTunde_Procunde_a)"
   by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Ver. (a_CONSTANTunde_Procunde_a~=zenon_Ver))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))", OF z_Hee])
   show FALSE
   by (rule zenon_noteq [OF z_Hei])
  qed
 next
  assume z_Hem:"(~?z_hdy)" (is "~(\\A x : ?z_hen(x))")
  have z_Heo: "(\\E zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg])))))" (is "\\E x : ?z_hep(x)")
  by (rule zenon_notallex_0 [of "?z_hen", OF z_Hem])
  have z_Heq: "?z_hep((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg]))))))" (is "~(?z_her=>?z_hdi)")
  by (rule zenon_ex_choose_0 [of "?z_hep", OF z_Heo])
  have z_Her: "?z_her"
  by (rule zenon_notimply_0 [OF z_Heq])
  have z_Hdc: "((?z_hr[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg])))))])~=(?z_hbt[(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg])))))]))" (is "?z_hdd~=?z_hde")
  by (rule zenon_notimply_1 [OF z_Heq])
  have z_Hdb: "((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg]))))) \\in a_CONSTANTunde_Procunde_a)" (is "?z_hdb")
  by (rule zenon_domain_fcn_0 [of "(\<lambda>zenon_Vzc. ((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg]))))) \\in zenon_Vzc))" "a_CONSTANTunde_Procunde_a" "(\<lambda>a_CONSTANTunde_punde_a_1. (CASE ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''a'', ''b''}) -> ''A'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1]) \\in {''c'', ''d''}) -> ''B'' [] ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a_1])=''e'') -> cond(((a_VARIABLEunde_lnbpartunde_a[a_CONSTANTunde_punde_a_1])=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_NUnionunde_a(a_VARIABLEunde_A2unde_a))), ''C'', ''B'')))", OF z_Her])
  show FALSE
  proof (rule notE [OF z_Hdc])
   have z_Hev: "(?z_hci=?z_hdd)"
   proof (rule zenon_nnpp [of "(?z_hci=?z_hdd)"])
    assume z_Hew:"(?z_hci~=?z_hdd)"
    show FALSE
    proof (rule zenon_em [of "(?z_hdd=?z_hdd)"])
     assume z_Hex:"(?z_hdd=?z_hdd)"
     show FALSE
     proof (rule notE [OF z_Hew])
      have z_Hey: "(?z_hdd=?z_hci)"
      proof (rule zenon_nnpp [of "(?z_hdd=?z_hci)"])
       assume z_Hez:"(?z_hdd~=?z_hci)"
       show FALSE
       proof (rule zenon_noteq [of "?z_hci"])
        have z_Hdn: "((CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg])))))=a_CONSTANTunde_punde_a)" (is "?z_hcs=_")
        proof (rule zenon_nnpp [of "(?z_hcs=a_CONSTANTunde_punde_a)"])
         assume z_Hcr:"(?z_hcs~=a_CONSTANTunde_punde_a)"
         show FALSE
         by (rule zenon_L1_ [OF z_Hck z_Hcr z_Hdb z_Hdc])
        qed
        have z_Hfa: "(?z_hci~=?z_hci)"
        by (rule subst [where P="(\<lambda>zenon_Vgr. ((?z_hr[zenon_Vgr])~=?z_hci))", OF z_Hdn], fact z_Hez)
        thus "(?z_hci~=?z_hci)" .
       qed
      qed
      have z_Hev: "(?z_hci=?z_hdd)"
      by (rule subst [where P="(\<lambda>zenon_Vhr. (zenon_Vhr=?z_hdd))", OF z_Hey], fact z_Hex)
      thus "(?z_hci=?z_hdd)" .
     qed
    next
     assume z_Hfi:"(?z_hdd~=?z_hdd)"
     show FALSE
     by (rule zenon_noteq [OF z_Hfi])
    qed
   qed
   have z_Hfj: "(?z_hcj=?z_hde)"
   proof (rule zenon_nnpp [of "(?z_hcj=?z_hde)"])
    assume z_Hfk:"(?z_hcj~=?z_hde)"
    show FALSE
    proof (rule zenon_noteq [of "?z_hde"])
     have z_Hfl: "(a_CONSTANTunde_punde_a=(CHOOSE zenon_Vg:(~((zenon_Vg \\in DOMAIN(?z_hbt))=>((?z_hr[zenon_Vg])=(?z_hbt[zenon_Vg]))))))" (is "_=?z_hcs")
     proof (rule zenon_nnpp [of "(a_CONSTANTunde_punde_a=?z_hcs)"])
      assume z_Hdp:"(a_CONSTANTunde_punde_a~=?z_hcs)"
      show FALSE
      by (rule zenon_L2_ [OF z_Hck z_Hdp z_Hdb z_Hdc])
     qed
     have z_Hfm: "(?z_hde~=?z_hde)"
     by (rule subst [where P="(\<lambda>zenon_Vir. ((?z_hbt[zenon_Vir])~=?z_hde))", OF z_Hfl], fact z_Hfk)
     thus "(?z_hde~=?z_hde)" .
    qed
   qed
   have z_Hfr: "(?z_hdd=?z_hcj)"
   by (rule subst [where P="(\<lambda>zenon_Vi. (zenon_Vi=?z_hcj))", OF z_Hev], fact z_Hh)
   have z_Hdi: "?z_hdi"
   by (rule subst [where P="(\<lambda>zenon_Vkr. (?z_hdd=zenon_Vkr))", OF z_Hfj], fact z_Hfr)
   thus "?z_hdi" .
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1683"; *} qed
end

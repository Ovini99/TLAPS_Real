(* automatically generated -- do not edit manually *)
theory GFX_test imports Constant Zenon begin
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

lemma ob'86:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition CONSTANT_ProcSet_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'51: "((((((((((a_VARIABLEunde_A1unde_a) \<in> ([(Nat) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_resultunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_pcunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ({(''a''), (''b''), (''Done'')})]))) & (((a_VARIABLEunde_knownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_notKnownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (Nat)))]))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))))))) \<and> (a_STATEunde_InvBunde_a))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'52: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'66: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'67: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'68: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'69: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'70: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
assumes v'71: "(((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<in> ((SUBSET (a_CONSTANTunde_Procunde_a)))))"
shows "((((a_VARIABLEunde_resultunde_hash_primea :: c)) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))])))"(is "PROP ?ob'86")
proof -
ML_command {* writeln "*** TLAPS ENTER 86"; *}
show "PROP ?ob'86"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_e1f814.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_e1f814.znn.out
;; obligation #86
$hyp "v'51" (/\ (/\ (/\ (/\ (TLA.in a_VARIABLEunde_A1unde_a
(TLA.FuncSet arith.N (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_resultunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_pcunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.set "a" "b" "Done")))
(TLA.in a_VARIABLEunde_knownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_notKnownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET arith.N)))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b") (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a)
TLA.emptyset)))))) a_STATEunde_InvBunde_a) a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'52" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'66" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'67" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'68" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'69" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'70" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$hyp "v'71" (TLA.in (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.SUBSET a_CONSTANTunde_Procunde_a))
$goal (TLA.in a_VARIABLEunde_resultunde_hash_primea
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((((a_VARIABLEunde_A1unde_a \\in FuncSet(Nat, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_resultunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''}))&((a_VARIABLEunde_knownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_notKnownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(Nat)))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})))))))))&a_STATEunde_InvBunde_a)&a_STATEunde_InvCunde_a)&a_STATEunde_GFXCorrectunde_a)" (is "?z_hk&_")
 using v'51 by blast
 have z_Hd:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hd")
 using v'66 by blast
 have z_Hi:"((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]) \\in SUBSET(a_CONSTANTunde_Procunde_a))" (is "?z_hi")
 using v'71 by blast
 have zenon_L1_: "(\\A zenon_Vjc:((a_VARIABLEunde_resultunde_hash_primea[zenon_Vjc])=(except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))[zenon_Vjc]))) ==> (a_CONSTANTunde_punde_a~=(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))) ==> ((a_VARIABLEunde_resultunde_a[(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))])~=(a_VARIABLEunde_resultunde_hash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))])) ==> ((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))) \\in DOMAIN(a_VARIABLEunde_resultunde_a)) ==> FALSE" (is "?z_hcp ==> ?z_hcu ==> ?z_hdc ==> ?z_hdf ==> FALSE")
 proof -
  assume z_Hcp:"?z_hcp" (is "\\A x : ?z_hdh(x)")
  assume z_Hcu:"?z_hcu" (is "_~=?z_hcv")
  assume z_Hdc:"?z_hdc" (is "?z_hdd~=?z_hde")
  assume z_Hdf:"?z_hdf"
  have z_Hdi: "?z_hdh(?z_hcv)" (is "_=?z_hdj")
  by (rule zenon_all_0 [of "?z_hdh" "?z_hcv", OF z_Hcp])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Veyb. (?z_hde=zenon_Veyb))" "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_punde_a" "(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])" "?z_hcv", OF z_Hdi])
   assume z_Hdf:"?z_hdf"
   assume z_Hdn:"(a_CONSTANTunde_punde_a=?z_hcv)"
   assume z_Hdo:"(?z_hde=(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))" (is "_=?z_hcl")
   show FALSE
   by (rule notE [OF z_Hcu z_Hdn])
  next
   assume z_Hdf:"?z_hdf"
   assume z_Hcu:"?z_hcu"
   assume z_Hdp:"(?z_hde=?z_hdd)"
   show FALSE
   by (rule zenon_eqsym [OF z_Hdp z_Hdc])
  next
   assume z_Hdq:"(~?z_hdf)"
   show FALSE
   by (rule notE [OF z_Hdq z_Hdf])
  qed
 qed
 assume z_Hj:"(~(a_VARIABLEunde_resultunde_hash_primea \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a))))" (is "~?z_hdr")
 have z_Hk: "?z_hk" (is "?z_hl&_")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hl: "?z_hl" (is "?z_hm&_")
 by (rule zenon_and_0 [OF z_Hk])
 have z_Hm: "?z_hm" (is "?z_hn&?z_ht")
 by (rule zenon_and_0 [OF z_Hl])
 have z_Ht: "?z_ht" (is "?z_hu&?z_hx")
 by (rule zenon_and_1 [OF z_Hm])
 have z_Hu: "?z_hu"
 by (rule zenon_and_0 [OF z_Ht])
 have z_Hx: "?z_hx" (is "?z_hy&?z_hbf")
 by (rule zenon_and_1 [OF z_Ht])
 have z_Hy: "?z_hy"
 by (rule zenon_and_0 [OF z_Hx])
 have z_Hds: "(DOMAIN(a_VARIABLEunde_resultunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hdg=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hu])
 have z_Hdt: "(DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hdu=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_Procunde_a" "{''a'', ''b'', ''Done''}", OF z_Hy])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hd])
  assume z_Hbz:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hca~=_")
  assume z_Hcc:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hcd&?z_hcg")
  have z_Hcg: "?z_hcg"
  by (rule zenon_and_1 [OF z_Hcc])
  show FALSE
  proof (rule notE [OF z_Hj])
   have z_Hdx: "(a_VARIABLEunde_resultunde_a=a_VARIABLEunde_resultunde_hash_primea)"
   by (rule sym [OF z_Hcg])
   have z_Hdr: "?z_hdr"
   by (rule subst [where P="(\<lambda>zenon_Veaf. (zenon_Veaf \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a))))", OF z_Hdx], fact z_Hu)
   thus "?z_hdr" .
  qed
 next
  assume z_Heb:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hec")
  assume z_Hci:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hcj&?z_hcn")
  have z_Hcj: "?z_hcj" (is "_=?z_hck")
  by (rule zenon_and_0 [OF z_Hci])
  have z_Hcn: "?z_hcn" (is "_=?z_hco")
  by (rule zenon_and_1 [OF z_Hci])
  show FALSE
  proof (rule zenon_notin_funcset [of "a_VARIABLEunde_resultunde_hash_primea" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hj])
   assume z_Hed:"(~isAFcn(a_VARIABLEunde_resultunde_hash_primea))" (is "~?z_hee")
   have z_Hef: "(~isAFcn(?z_hck))" (is "~?z_heg")
   by (rule subst [where P="(\<lambda>zenon_Vazd. (~isAFcn(zenon_Vazd)))", OF z_Hcj z_Hed])
   show FALSE
   by (rule zenon_notisafcn_except [of "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_punde_a" "(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])", OF z_Hef])
  next
   assume z_Hel:"(DOMAIN(a_VARIABLEunde_resultunde_hash_primea)~=a_CONSTANTunde_Procunde_a)" (is "?z_hem~=_")
   have z_Hen: "(DOMAIN(?z_hck)~=a_CONSTANTunde_Procunde_a)" (is "?z_heo~=_")
   by (rule subst [where P="(\<lambda>zenon_Vezd. (DOMAIN(zenon_Vezd)~=a_CONSTANTunde_Procunde_a))", OF z_Hcj z_Hel])
   have z_Het: "(?z_hdg~=a_CONSTANTunde_Procunde_a)"
   by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vdzd. (zenon_Vdzd~=a_CONSTANTunde_Procunde_a))" "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_punde_a" "(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])", OF z_Hen])
   show FALSE
   by (rule notE [OF z_Het z_Hds])
  next
   assume z_Hex:"(~(\\A zenon_Vh:((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))" (is "~(\\A x : ?z_hez(x))")
   have z_Hfa: "(\\E zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))" (is "\\E x : ?z_hfb(x)")
   by (rule zenon_notallex_0 [of "?z_hez", OF z_Hex])
   have z_Hfc: "?z_hfb((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))))" (is "~(?z_hfd=>?z_hfe)")
   by (rule zenon_ex_choose_0 [of "?z_hfb", OF z_Hfa])
   have z_Hfd: "?z_hfd"
   by (rule zenon_notimply_0 [OF z_Hfc])
   have z_Hff: "(~?z_hfe)"
   by (rule zenon_notimply_1 [OF z_Hfc])
   have z_Hdf: "((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))) \\in ?z_hdg)" (is "?z_hdf")
   by (rule ssubst [where P="(\<lambda>zenon_Vwd. ((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))) \\in zenon_Vwd))", OF z_Hds z_Hfd])
   have z_Hfj: "((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))) \\in ?z_hdu)" (is "?z_hfj")
   by (rule ssubst [where P="(\<lambda>zenon_Vwd. ((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))) \\in zenon_Vwd))", OF z_Hdt z_Hfd])
   show FALSE
   proof (rule notE [OF z_Hff])
    have z_Hfk: "((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_resultunde_hash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))]))" (is "?z_hcl=?z_hde")
    proof (rule zenon_nnpp [of "(?z_hcl=?z_hde)"])
     assume z_Hfl:"(?z_hcl~=?z_hde)"
     have z_Hfm: "(\\A zenon_Vfa:((zenon_Vfa \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_a[zenon_Vfa]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))" (is "\\A x : ?z_hfs(x)")
     by (rule zenon_in_funcset_2 [of "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hu])
     have z_Hft: "?z_hfs((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))))" (is "_=>?z_hfu")
     by (rule zenon_all_0 [of "?z_hfs" "(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))", OF z_Hfm])
     show FALSE
     proof (rule zenon_imply [OF z_Hft])
      assume z_Hfv:"(~?z_hfd)"
      show FALSE
      by (rule notE [OF z_Hfv z_Hfd])
     next
      assume z_Hfu:"?z_hfu"
      show FALSE
      proof (rule notE [OF z_Hff])
       have z_Hfw: "((a_VARIABLEunde_resultunde_a[(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))])=?z_hde)" (is "?z_hdd=_")
       proof (rule zenon_nnpp [of "(?z_hdd=?z_hde)"])
        assume z_Hdc:"(?z_hdd~=?z_hde)"
        have z_Hfx: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_hco))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_hco)))&(\\A zenon_Vhc:((a_VARIABLEunde_pcunde_hash_primea[zenon_Vhc])=(?z_hco[zenon_Vhc]))))" (is "?z_hfy&?z_hgf")
        by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_hco", OF z_Hcn])
        have z_Hgf: "?z_hgf" (is "\\A x : ?z_hgk(x)")
        by (rule zenon_and_1 [OF z_Hfx])
        have z_Hgl: "(((isAFcn(a_VARIABLEunde_resultunde_hash_primea)<=>isAFcn(?z_hck))&(DOMAIN(a_VARIABLEunde_resultunde_hash_primea)=DOMAIN(?z_hck)))&(\\A zenon_Vjc:((a_VARIABLEunde_resultunde_hash_primea[zenon_Vjc])=(?z_hck[zenon_Vjc]))))" (is "?z_hgm&?z_hcp")
        by (rule zenon_funequal_0 [of "a_VARIABLEunde_resultunde_hash_primea" "?z_hck", OF z_Hcj])
        have z_Hcp: "?z_hcp" (is "\\A x : ?z_hdh(x)")
        by (rule zenon_and_1 [OF z_Hgl])
        have z_Hgp: "?z_hgk((CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))))" (is "?z_hgq=?z_hgr")
        by (rule zenon_all_0 [of "?z_hgk" "(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))", OF z_Hgf])
        show FALSE
        proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vcyb. (?z_hgq=zenon_Vcyb))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "''Done''" "(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a)))))", OF z_Hgp])
         assume z_Hfj:"?z_hfj"
         assume z_Hdn:"(a_CONSTANTunde_punde_a=(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))))" (is "_=?z_hcv")
         assume z_Hgv:"(?z_hgq=''Done'')" (is "_=?z_hbe")
         have z_Hdi: "?z_hdh(?z_hcv)" (is "_=?z_hdj")
         by (rule zenon_all_0 [of "?z_hdh" "?z_hcv", OF z_Hcp])
         show FALSE
         proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Veyb. (?z_hde=zenon_Veyb))" "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_punde_a" "?z_hcl" "?z_hcv", OF z_Hdi])
          assume z_Hdf:"?z_hdf"
          assume z_Hdn:"(a_CONSTANTunde_punde_a=?z_hcv)"
          assume z_Hdo:"(?z_hde=?z_hcl)"
          show FALSE
          by (rule zenon_eqsym [OF z_Hdo z_Hfl])
         next
          assume z_Hdf:"?z_hdf"
          assume z_Hcu:"(a_CONSTANTunde_punde_a~=?z_hcv)"
          assume z_Hdp:"(?z_hde=?z_hdd)"
          show FALSE
          by (rule notE [OF z_Hcu z_Hdn])
         next
          assume z_Hdq:"(~?z_hdf)"
          show FALSE
          by (rule notE [OF z_Hdq z_Hdf])
         qed
        next
         assume z_Hfj:"?z_hfj"
         assume z_Hcu:"(a_CONSTANTunde_punde_a~=(CHOOSE zenon_Vh:(~((zenon_Vh \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_resultunde_hash_primea[zenon_Vh]) \\in SUBSET(a_CONSTANTunde_Procunde_a))))))" (is "_~=?z_hcv")
         assume z_Hgw:"(?z_hgq=(a_VARIABLEunde_pcunde_a[?z_hcv]))" (is "_=?z_hgx")
         show FALSE
         by (rule zenon_L1_ [OF z_Hcp z_Hcu z_Hdc z_Hdf])
        next
         assume z_Hgy:"(~?z_hfj)"
         show FALSE
         by (rule notE [OF z_Hgy z_Hfj])
        qed
       qed
       have z_Hfe: "?z_hfe"
       by (rule subst [where P="(\<lambda>zenon_Vi. (zenon_Vi \\in SUBSET(a_CONSTANTunde_Procunde_a)))", OF z_Hfw], fact z_Hfu)
       thus "?z_hfe" .
      qed
     qed
    qed
    have z_Hfe: "?z_hfe"
    by (rule subst [where P="(\<lambda>zenon_Vi. (zenon_Vi \\in SUBSET(a_CONSTANTunde_Procunde_a)))", OF z_Hfk], fact z_Hi)
    thus "?z_hfe" .
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 86"; *} qed
lemma ob'109:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition CONSTANT_ProcSet_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'51: "((((((((((a_VARIABLEunde_A1unde_a) \<in> ([(Nat) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_resultunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_pcunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ({(''a''), (''b''), (''Done'')})]))) & (((a_VARIABLEunde_knownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_notKnownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (Nat)))]))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))))))) \<and> (a_STATEunde_InvBunde_a))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'52: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'70: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'71: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'72: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'73: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'74: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
assumes v'75: "((((a_CONSTANTunde_IsFiniteSetunde_a ((a_STATEunde_snapshotunde_a)))) \<and> (((a_STATEunde_snapshotunde_a) \<subseteq> (a_CONSTANTunde_Procunde_a)))))"
assumes v'76: "(\<forall>a_CONSTANTunde_Sunde_a : ((((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_Sunde_a)))) \<Rightarrow> ((((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_Sunde_a)))) \<in> (Nat))))))"
assumes v'77: "((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_Procunde_a))))"
assumes v'78: "(\<forall>a_CONSTANTunde_Sunde_a : ((((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_Sunde_a)))) \<Rightarrow> (\<forall> a_CONSTANTunde_Tunde_a \<in> ((SUBSET (a_CONSTANTunde_Sunde_a))) : ((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_Tunde_a))))))))"
shows "(\<forall> a_CONSTANTunde_punde_1unde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (''b''))) \<Rightarrow> (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) \<noteq> ({}))))))"(is "PROP ?ob'109")
proof -
ML_command {* writeln "*** TLAPS ENTER 109"; *}
show "PROP ?ob'109"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_507de6.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_507de6.znn.out
;; obligation #109
$hyp "v'51" (/\ (/\ (/\ (/\ (TLA.in a_VARIABLEunde_A1unde_a
(TLA.FuncSet arith.N (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_resultunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_pcunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.set "a" "b" "Done")))
(TLA.in a_VARIABLEunde_knownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_notKnownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET arith.N)))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b") (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a)
TLA.emptyset)))))) a_STATEunde_InvBunde_a) a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'52" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'70" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'71" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'72" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'73" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'74" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$hyp "v'75" (/\ (a_CONSTANTunde_IsFiniteSetunde_a a_STATEunde_snapshotunde_a)
(TLA.subseteq a_STATEunde_snapshotunde_a
a_CONSTANTunde_Procunde_a))
$hyp "v'76" (A. ((a_CONSTANTunde_Sunde_a) (=> (a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_Sunde_a)
(TLA.in (a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_Sunde_a)
arith.N))))
$hyp "v'77" (a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_Procunde_a)
$hyp "v'78" (A. ((a_CONSTANTunde_Sunde_a) (=> (a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_Sunde_a)
(TLA.bAll (TLA.SUBSET a_CONSTANTunde_Sunde_a) ((a_CONSTANTunde_Tunde_a) (a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_Tunde_a))))))
$goal (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_1unde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_1unde_a)
"b")
(-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_1unde_a)
TLA.emptyset)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((((a_VARIABLEunde_A1unde_a \\in FuncSet(Nat, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_resultunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''}))&((a_VARIABLEunde_knownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_notKnownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(Nat)))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})))))))))&a_STATEunde_InvBunde_a)&a_STATEunde_InvCunde_a)&a_STATEunde_GFXCorrectunde_a)" (is "?z_hn&_")
 using v'51 by blast
 have z_Hg:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hcd")
 using v'73 by blast
 have z_Hd:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hd")
 using v'70 by blast
 have z_Hc:"(a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hc")
 using a_CONSTANTunde_punde_a_in by blast
 have zenon_L1_: "(\\A zenon_Vac:((zenon_Vac \\in DOMAIN(a_VARIABLEunde_pcunde_a))<=>(zenon_Vac \\in a_CONSTANTunde_Procunde_a))) ==> ((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in a_CONSTANTunde_Procunde_a) ==> (~((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in DOMAIN(a_VARIABLEunde_pcunde_a))) ==> FALSE" (is "?z_hdb ==> ?z_hdh ==> ?z_hds ==> FALSE")
 proof -
  assume z_Hdb:"?z_hdb" (is "\\A x : ?z_hdu(x)")
  assume z_Hdh:"?z_hdh"
  assume z_Hds:"?z_hds" (is "~?z_hdt")
  have z_Hdv: "?z_hdu((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))))"
  by (rule zenon_all_0 [of "?z_hdu" "(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={})))))", OF z_Hdb])
  show FALSE
  proof (rule zenon_equiv [OF z_Hdv])
   assume z_Hds:"?z_hds"
   assume z_Hdw:"(~?z_hdh)"
   show FALSE
   by (rule notE [OF z_Hdw z_Hdh])
  next
   assume z_Hdt:"?z_hdt"
   assume z_Hdh:"?z_hdh"
   show FALSE
   by (rule notE [OF z_Hds z_Hdt])
  qed
 qed
 have zenon_L2_: "(DOMAIN(a_VARIABLEunde_knownunde_a)~=DOMAIN(a_VARIABLEunde_notKnownunde_a)) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> FALSE" (is "?z_hdx ==> ?z_hea ==> ?z_heb ==> FALSE")
 proof -
  assume z_Hdx:"?z_hdx" (is "?z_hdy~=?z_hdz")
  assume z_Hea:"?z_hea"
  assume z_Heb:"?z_heb"
  show FALSE
  proof (rule notE [OF z_Hdx])
   have z_Hec: "(a_CONSTANTunde_Procunde_a=?z_hdz)"
   by (rule sym [OF z_Heb])
   have z_Hed: "(?z_hdy=?z_hdz)"
   by (rule subst [where P="(\<lambda>zenon_Vnxg. (?z_hdy=zenon_Vnxg))", OF z_Hec], fact z_Hea)
   thus "(?z_hdy=?z_hdz)" .
  qed
 qed
 have zenon_L3_: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> (~((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in DOMAIN(a_VARIABLEunde_notKnownunde_a))) ==> ((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in a_CONSTANTunde_Procunde_a) ==> FALSE" (is "?z_hea ==> ?z_heb ==> ?z_heh ==> ?z_hdh ==> FALSE")
 proof -
  assume z_Hea:"?z_hea" (is "?z_hdy=_")
  assume z_Heb:"?z_heb" (is "?z_hdz=_")
  assume z_Heh:"?z_heh" (is "~?z_hei")
  assume z_Hdh:"?z_hdh"
  have z_Hej: "(\\A zenon_Vfc:((zenon_Vfc \\in ?z_hdy)<=>(zenon_Vfc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_heo(x)")
  by (rule zenon_setequal_0 [of "?z_hdy" "a_CONSTANTunde_Procunde_a", OF z_Hea])
  have z_Hep: "?z_heo((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))))" (is "?z_heq<=>_")
  by (rule zenon_all_0 [of "?z_heo" "(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={})))))", OF z_Hej])
  show FALSE
  proof (rule zenon_equiv [OF z_Hep])
   assume z_Her:"(~?z_heq)"
   assume z_Hdw:"(~?z_hdh)"
   show FALSE
   by (rule notE [OF z_Hdw z_Hdh])
  next
   assume z_Heq:"?z_heq"
   assume z_Hdh:"?z_hdh"
   show FALSE
   proof (rule notE [OF z_Heh])
    have z_Hed: "(?z_hdy=?z_hdz)"
    proof (rule zenon_nnpp [of "(?z_hdy=?z_hdz)"])
     assume z_Hdx:"(?z_hdy~=?z_hdz)"
     show FALSE
     by (rule zenon_L2_ [OF z_Hdx z_Hea z_Heb])
    qed
    have z_Hei: "?z_hei"
    by (rule subst [where P="(\<lambda>zenon_Voxg. ((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in zenon_Voxg))", OF z_Hed], fact z_Heq)
    thus "?z_hei" .
   qed
  qed
 qed
 have zenon_L4_: "(~(a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_notKnownunde_a))) ==> (a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> FALSE" (is "?z_hev ==> ?z_hex ==> ?z_heb ==> ?z_hea ==> FALSE")
 proof -
  assume z_Hev:"?z_hev" (is "~?z_hew")
  assume z_Hex:"?z_hex"
  assume z_Heb:"?z_heb" (is "?z_hdz=_")
  assume z_Hea:"?z_hea" (is "?z_hdy=_")
  show FALSE
  proof (rule notE [OF z_Hev])
   have z_Hed: "(?z_hdy=?z_hdz)"
   proof (rule zenon_nnpp [of "(?z_hdy=?z_hdz)"])
    assume z_Hdx:"(?z_hdy~=?z_hdz)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hdx z_Hea z_Heb])
   qed
   have z_Hew: "?z_hew"
   by (rule subst [where P="(\<lambda>zenon_Vpxg. (a_CONSTANTunde_punde_a \\in zenon_Vpxg))", OF z_Hed], fact z_Hex)
   thus "?z_hew" .
  qed
 qed
 have zenon_L5_: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> (~(a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_notKnownunde_a))) ==> ?z_hc ==> FALSE" (is "?z_hea ==> ?z_heb ==> ?z_hev ==> _ ==> FALSE")
 proof -
  assume z_Hea:"?z_hea" (is "?z_hdy=_")
  assume z_Heb:"?z_heb" (is "?z_hdz=_")
  assume z_Hev:"?z_hev" (is "~?z_hew")
  assume z_Hc:"?z_hc"
  have z_Hej: "(\\A zenon_Vfc:((zenon_Vfc \\in ?z_hdy)<=>(zenon_Vfc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_heo(x)")
  by (rule zenon_setequal_0 [of "?z_hdy" "a_CONSTANTunde_Procunde_a", OF z_Hea])
  have z_Hfb: "?z_heo(a_CONSTANTunde_punde_a)" (is "?z_hex<=>_")
  by (rule zenon_all_0 [of "?z_heo" "a_CONSTANTunde_punde_a", OF z_Hej])
  show FALSE
  proof (rule zenon_equiv [OF z_Hfb])
   assume z_Hfc:"(~?z_hex)"
   assume z_Hfd:"(~?z_hc)"
   show FALSE
   by (rule notE [OF z_Hfd z_Hc])
  next
   assume z_Hex:"?z_hex"
   assume z_Hc:"?z_hc"
   show FALSE
   by (rule zenon_L4_ [OF z_Hev z_Hex z_Heb z_Hea])
  qed
 qed
 assume z_Hm:"(~bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_1unde_a. (((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~={})))))" (is "~?z_hfe")
 have z_Hn: "?z_hn" (is "?z_ho&_")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Ho: "?z_ho" (is "?z_hp&_")
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hp: "?z_hp" (is "?z_hq&?z_hw")
 by (rule zenon_and_0 [OF z_Ho])
 have z_Hw: "?z_hw" (is "?z_hx&?z_hba")
 by (rule zenon_and_1 [OF z_Hp])
 have z_Hba: "?z_hba" (is "?z_hbb&?z_hbi")
 by (rule zenon_and_1 [OF z_Hw])
 have z_Hbb: "?z_hbb"
 by (rule zenon_and_0 [OF z_Hba])
 have z_Hbi: "?z_hbi" (is "?z_hbj&?z_hbl")
 by (rule zenon_and_1 [OF z_Hba])
 have z_Hbj: "?z_hbj"
 by (rule zenon_and_0 [OF z_Hbi])
 have z_Hbl: "?z_hbl" (is "?z_hbm&?z_hbq")
 by (rule zenon_and_1 [OF z_Hbi])
 have z_Hbm: "?z_hbm"
 by (rule zenon_and_0 [OF z_Hbl])
 have z_Hbq: "?z_hbq"
 by (rule zenon_and_1 [OF z_Hbl])
 have z_Hfm_z_Hbq: "(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_a[x])=''b'')=>((a_VARIABLEunde_notKnownunde_a[x])~={})))) == ?z_hbq" (is "?z_hfm == _")
 by (unfold bAll_def)
 have z_Hfm: "?z_hfm" (is "\\A x : ?z_hft(x)")
 by (unfold z_Hfm_z_Hbq, fact z_Hbq)
 have z_Hfu_z_Hm: "(~(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) == (~?z_hfe)" (is "?z_hfu == ?z_hm")
 by (unfold bAll_def)
 have z_Hfu: "?z_hfu" (is "~(\\A x : ?z_hfw(x))")
 by (unfold z_Hfu_z_Hm, fact z_Hm)
 have z_Hfx: "(\\E x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={})))))" (is "\\E x : ?z_hfy(x)")
 by (rule zenon_notallex_0 [of "?z_hfw", OF z_Hfu])
 have z_Hfz: "?z_hfy((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=''b'')=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))))" (is "~(?z_hdh=>?z_hga)")
 by (rule zenon_ex_choose_0 [of "?z_hfy", OF z_Hfx])
 have z_Hdh: "?z_hdh"
 by (rule zenon_notimply_0 [OF z_Hfz])
 have z_Hgb: "(~?z_hga)" (is "~(?z_hgc=>?z_hgd)")
 by (rule zenon_notimply_1 [OF z_Hfz])
 have z_Hgc: "?z_hgc" (is "?z_hge=?z_hbg")
 by (rule zenon_notimply_0 [OF z_Hgb])
 have z_Hgf: "(~?z_hgd)" (is "~~?z_hgg")
 by (rule zenon_notimply_1 [OF z_Hgb])
 have z_Hgg: "?z_hgg" (is "?z_hgh=_")
 by (rule zenon_notnot_0 [OF z_Hgf])
 have z_Hgi: "((?z_hcd[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={})))))])={})" (is "?z_hgj=_")
 by (rule subst [where P="(\<lambda>zenon_Vkxg. ((zenon_Vkxg[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={})))))])={}))", OF z_Hg z_Hgg])
 have z_Hgo: "(DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hdf=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_Procunde_a" "{''a'', ?z_hbg, ''Done''}", OF z_Hbb])
 have z_Hea: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hdy=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hbj])
 have z_Heb: "(DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hdz=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(Nat)", OF z_Hbm])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ?z_hbg))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hd])
  assume z_Hco:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hcp~=_")
  assume z_Hcq:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ?z_hbg))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hcr&?z_hcu")
  have z_Hcr: "?z_hcr" (is "_=?z_hct")
  by (rule zenon_and_0 [OF z_Hcq])
  have z_Hgr: "((?z_hcd[a_CONSTANTunde_punde_a])~={})" (is "?z_hgs~=_")
  by (rule subst [where P="(\<lambda>zenon_Vmxg. ((zenon_Vmxg[a_CONSTANTunde_punde_a])~={}))", OF z_Hg z_Hco])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vnsb. (zenon_Vnsb~={}))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))" "a_CONSTANTunde_punde_a", OF z_Hgr])
   assume z_Hew:"(a_CONSTANTunde_punde_a \\in ?z_hdz)" (is "?z_hew")
   assume z_Hha:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_a)"
   assume z_Hhb:"(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))~={})" (is "?z_hce~=_")
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vra. (zenon_Vra={}))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "?z_hce" "(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={})))))", OF z_Hgi])
    assume z_Hei:"((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in ?z_hdz)" (is "?z_hei")
    assume z_Hhf:"(a_CONSTANTunde_punde_a=(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))))" (is "_=?z_hdi")
    assume z_Hhg:"(?z_hce={})"
    show FALSE
    by (rule notE [OF z_Hhb z_Hhg])
   next
    assume z_Hei:"((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in ?z_hdz)" (is "?z_hei")
    assume z_Hhh:"(a_CONSTANTunde_punde_a~=(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))))" (is "_~=?z_hdi")
    assume z_Hhi:"((a_VARIABLEunde_notKnownunde_a[?z_hdi])={})" (is "?z_hhj=_")
    have z_Hhk: "?z_hft(?z_hdi)" (is "_=>?z_hhl")
    by (rule zenon_all_0 [of "?z_hft" "?z_hdi", OF z_Hfm])
    show FALSE
    proof (rule zenon_imply [OF z_Hhk])
     assume z_Hdw:"(~?z_hdh)"
     show FALSE
     by (rule notE [OF z_Hdw z_Hdh])
    next
     assume z_Hhl:"?z_hhl" (is "?z_hhm=>?z_hhn")
     show FALSE
     proof (rule zenon_imply [OF z_Hhl])
      assume z_Hho:"((a_VARIABLEunde_pcunde_a[?z_hdi])~=?z_hbg)" (is "?z_hhp~=_")
      show FALSE
      proof (rule notE [OF z_Hho])
       have z_Hhq: "(?z_hge=?z_hhp)"
       proof (rule zenon_nnpp [of "(?z_hge=?z_hhp)"])
        assume z_Hhr:"(?z_hge~=?z_hhp)"
        show FALSE
        proof (rule zenon_em [of "(?z_hhp=?z_hhp)"])
         assume z_Hhs:"(?z_hhp=?z_hhp)"
         show FALSE
         proof (rule notE [OF z_Hhr])
          have z_Hht: "(?z_hhp=?z_hge)"
          proof (rule zenon_nnpp [of "(?z_hhp=?z_hge)"])
           assume z_Hhu:"(?z_hhp~=?z_hge)"
           have z_Hdb: "(\\A zenon_Vac:((zenon_Vac \\in ?z_hdf)<=>(zenon_Vac \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hdu(x)")
           by (rule zenon_setequal_0 [of "?z_hdf" "a_CONSTANTunde_Procunde_a", OF z_Hgo])
           have z_Hhv: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_hct))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_hct)))&(\\A zenon_Vrsb:((a_VARIABLEunde_pcunde_hash_primea[zenon_Vrsb])=(?z_hct[zenon_Vrsb]))))" (is "?z_hhw&?z_hid")
           by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_hct", OF z_Hcr])
           have z_Hid: "?z_hid" (is "\\A x : ?z_hii(x)")
           by (rule zenon_and_1 [OF z_Hhv])
           have z_Hij: "?z_hii(?z_hdi)" (is "_=?z_hik")
           by (rule zenon_all_0 [of "?z_hii" "?z_hdi", OF z_Hid])
           show FALSE
           proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vnrb. (?z_hge=zenon_Vnrb))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "?z_hbg" "?z_hdi", OF z_Hij])
            assume z_Hdt:"(?z_hdi \\in ?z_hdf)" (is "?z_hdt")
            assume z_Hhf:"(a_CONSTANTunde_punde_a=?z_hdi)"
            assume z_Hgc:"?z_hgc"
            show FALSE
            by (rule notE [OF z_Hhh z_Hhf])
           next
            assume z_Hdt:"(?z_hdi \\in ?z_hdf)" (is "?z_hdt")
            assume z_Hhh:"(a_CONSTANTunde_punde_a~=?z_hdi)"
            assume z_Hhq:"(?z_hge=?z_hhp)"
            show FALSE
            by (rule zenon_eqsym [OF z_Hhq z_Hhu])
           next
            assume z_Hds:"(~(?z_hdi \\in ?z_hdf))" (is "~?z_hdt")
            show FALSE
            by (rule zenon_L1_ [OF z_Hdb z_Hdh z_Hds])
           qed
          qed
          have z_Hhq: "(?z_hge=?z_hhp)"
          by (rule subst [where P="(\<lambda>zenon_Vqxg. (zenon_Vqxg=?z_hhp))", OF z_Hht], fact z_Hhs)
          thus "(?z_hge=?z_hhp)" .
         qed
        next
         assume z_Hir:"(?z_hhp~=?z_hhp)"
         show FALSE
         by (rule zenon_noteq [OF z_Hir])
        qed
       qed
       have z_Hhm: "?z_hhm"
       by (rule subst [where P="(\<lambda>zenon_Vrxg. (zenon_Vrxg=?z_hbg))", OF z_Hhq], fact z_Hgc)
       thus "?z_hhm" .
      qed
     next
      assume z_Hhn:"?z_hhn"
      show FALSE
      by (rule notE [OF z_Hhn z_Hhi])
     qed
    qed
   next
    assume z_Heh:"(~((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in ?z_hdz))" (is "~?z_hei")
    show FALSE
    by (rule zenon_L3_ [OF z_Hea z_Heb z_Heh z_Hdh])
   qed
  next
   assume z_Hew:"(a_CONSTANTunde_punde_a \\in ?z_hdz)" (is "?z_hew")
   assume z_Hiv:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_a)"
   assume z_Hbw:"((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})" (is "?z_hbx~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hiv])
  next
   assume z_Hev:"(~(a_CONSTANTunde_punde_a \\in ?z_hdz))" (is "~?z_hew")
   show FALSE
   by (rule zenon_L5_ [OF z_Hea z_Heb z_Hev z_Hc])
  qed
 next
  assume z_Hiw:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hix")
  assume z_Hcw:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hcx&?z_hcz")
  have z_Hcz: "?z_hcz" (is "_=?z_hda")
  by (rule zenon_and_1 [OF z_Hcw])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vra. (zenon_Vra={}))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))" "(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={})))))", OF z_Hgi])
   assume z_Hei:"((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in ?z_hdz)" (is "?z_hei")
   assume z_Hhf:"(a_CONSTANTunde_punde_a=(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))))" (is "_=?z_hdi")
   assume z_Hhg:"(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))={})" (is "?z_hce=_")
   have z_Hdb: "(\\A zenon_Vac:((zenon_Vac \\in ?z_hdf)<=>(zenon_Vac \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hdu(x)")
   by (rule zenon_setequal_0 [of "?z_hdf" "a_CONSTANTunde_Procunde_a", OF z_Hgo])
   have z_Hiy: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_hda))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_hda)))&(\\A zenon_Ved:((a_VARIABLEunde_pcunde_hash_primea[zenon_Ved])=(?z_hda[zenon_Ved]))))" (is "?z_hiz&?z_hje")
   by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_hda", OF z_Hcz])
   have z_Hje: "?z_hje" (is "\\A x : ?z_hjj(x)")
   by (rule zenon_and_1 [OF z_Hiy])
   have z_Hdv: "?z_hdu(?z_hdi)" (is "?z_hdt<=>_")
   by (rule zenon_all_0 [of "?z_hdu" "?z_hdi", OF z_Hdb])
   show FALSE
   proof (rule zenon_equiv [OF z_Hdv])
    assume z_Hds:"(~?z_hdt)"
    assume z_Hdw:"(~?z_hdh)"
    show FALSE
    by (rule notE [OF z_Hdw z_Hdh])
   next
    assume z_Hdt:"?z_hdt"
    assume z_Hdh:"?z_hdh"
    have z_Hjk: "?z_hjj(?z_hdi)" (is "_=?z_hjl")
    by (rule zenon_all_0 [of "?z_hjj" "?z_hdi", OF z_Hje])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vnrb. (?z_hge=zenon_Vnrb))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "''Done''" "?z_hdi", OF z_Hjk])
     assume z_Hdt:"?z_hdt"
     assume z_Hhf:"(a_CONSTANTunde_punde_a=?z_hdi)"
     assume z_Hjm:"(?z_hge=''Done'')" (is "_=?z_hbh")
     have z_Hjn: "(?z_hbh~=?z_hbg)"
     by auto
     have z_Hjo: "(?z_hge~=?z_hge)"
     by (rule zenon_stringdiffll [OF z_Hjn z_Hjm z_Hgc])
      show FALSE
      by (rule zenon_noteq [OF z_Hjo])
    next
     assume z_Hdt:"?z_hdt"
     assume z_Hhh:"(a_CONSTANTunde_punde_a~=?z_hdi)"
     assume z_Hhq:"(?z_hge=(a_VARIABLEunde_pcunde_a[?z_hdi]))" (is "_=?z_hhp")
     show FALSE
     by (rule notE [OF z_Hhh z_Hhf])
    next
     assume z_Hds:"(~?z_hdt)"
     show FALSE
     by (rule notE [OF z_Hds z_Hdt])
    qed
   qed
  next
   assume z_Hei:"((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in ?z_hdz)" (is "?z_hei")
   assume z_Hhh:"(a_CONSTANTunde_punde_a~=(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))))" (is "_~=?z_hdi")
   assume z_Hhi:"((a_VARIABLEunde_notKnownunde_a[?z_hdi])={})" (is "?z_hhj=_")
   have z_Hhk: "?z_hft(?z_hdi)" (is "_=>?z_hhl")
   by (rule zenon_all_0 [of "?z_hft" "?z_hdi", OF z_Hfm])
   show FALSE
   proof (rule zenon_imply [OF z_Hhk])
    assume z_Hdw:"(~?z_hdh)"
    show FALSE
    by (rule notE [OF z_Hdw z_Hdh])
   next
    assume z_Hhl:"?z_hhl" (is "?z_hhm=>?z_hhn")
    show FALSE
    proof (rule zenon_imply [OF z_Hhl])
     assume z_Hho:"((a_VARIABLEunde_pcunde_a[?z_hdi])~=?z_hbg)" (is "?z_hhp~=_")
     show FALSE
     proof (rule notE [OF z_Hho])
      have z_Hhq: "(?z_hge=?z_hhp)"
      proof (rule zenon_nnpp [of "(?z_hge=?z_hhp)"])
       assume z_Hhr:"(?z_hge~=?z_hhp)"
       show FALSE
       proof (rule zenon_em [of "(?z_hhp=?z_hhp)"])
        assume z_Hhs:"(?z_hhp=?z_hhp)"
        show FALSE
        proof (rule notE [OF z_Hhr])
         have z_Hht: "(?z_hhp=?z_hge)"
         proof (rule zenon_nnpp [of "(?z_hhp=?z_hge)"])
          assume z_Hhu:"(?z_hhp~=?z_hge)"
          have z_Hdb: "(\\A zenon_Vac:((zenon_Vac \\in ?z_hdf)<=>(zenon_Vac \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hdu(x)")
          by (rule zenon_setequal_0 [of "?z_hdf" "a_CONSTANTunde_Procunde_a", OF z_Hgo])
          have z_Hiy: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_hda))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_hda)))&(\\A zenon_Ved:((a_VARIABLEunde_pcunde_hash_primea[zenon_Ved])=(?z_hda[zenon_Ved]))))" (is "?z_hiz&?z_hje")
          by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_hda", OF z_Hcz])
          have z_Hje: "?z_hje" (is "\\A x : ?z_hjj(x)")
          by (rule zenon_and_1 [OF z_Hiy])
          have z_Hjk: "?z_hjj(?z_hdi)" (is "_=?z_hjl")
          by (rule zenon_all_0 [of "?z_hjj" "?z_hdi", OF z_Hje])
          show FALSE
          proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vnrb. (?z_hge=zenon_Vnrb))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "''Done''" "?z_hdi", OF z_Hjk])
           assume z_Hdt:"(?z_hdi \\in ?z_hdf)" (is "?z_hdt")
           assume z_Hhf:"(a_CONSTANTunde_punde_a=?z_hdi)"
           assume z_Hjm:"(?z_hge=''Done'')" (is "_=?z_hbh")
           show FALSE
           by (rule notE [OF z_Hhh z_Hhf])
          next
           assume z_Hdt:"(?z_hdi \\in ?z_hdf)" (is "?z_hdt")
           assume z_Hhh:"(a_CONSTANTunde_punde_a~=?z_hdi)"
           assume z_Hhq:"(?z_hge=?z_hhp)"
           show FALSE
           by (rule zenon_eqsym [OF z_Hhq z_Hhu])
          next
           assume z_Hds:"(~(?z_hdi \\in ?z_hdf))" (is "~?z_hdt")
           show FALSE
           by (rule zenon_L1_ [OF z_Hdb z_Hdh z_Hds])
          qed
         qed
         have z_Hhq: "(?z_hge=?z_hhp)"
         by (rule subst [where P="(\<lambda>zenon_Vqxg. (zenon_Vqxg=?z_hhp))", OF z_Hht], fact z_Hhs)
         thus "(?z_hge=?z_hhp)" .
        qed
       next
        assume z_Hir:"(?z_hhp~=?z_hhp)"
        show FALSE
        by (rule zenon_noteq [OF z_Hir])
       qed
      qed
      have z_Hhm: "?z_hhm"
      by (rule subst [where P="(\<lambda>zenon_Vrxg. (zenon_Vrxg=?z_hbg))", OF z_Hhq], fact z_Hgc)
      thus "?z_hhm" .
     qed
    next
     assume z_Hhn:"?z_hhn"
     show FALSE
     by (rule notE [OF z_Hhn z_Hhi])
    qed
   qed
  next
   assume z_Heh:"(~((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((a_VARIABLEunde_pcunde_hash_primea[x])=?z_hbg)=>((a_VARIABLEunde_notKnownunde_hash_primea[x])~={}))))) \\in ?z_hdz))" (is "~?z_hei")
   show FALSE
   by (rule zenon_L3_ [OF z_Hea z_Heb z_Heh z_Hdh])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 109"; *} qed
lemma ob'225:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'51: "(((((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_InvBunde_a))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'52: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'69: "((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a)))))), ((0)))))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h003cd :: c)))"
assumes v'73: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'74: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
assumes v'79: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'80: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'81: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'82: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'83: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
assumes v'84: "(((((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))) \<Longrightarrow> (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))))))))) | (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a))))))))))))"
assumes v'85: "(((((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({}))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')])))) \<Longrightarrow> (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))))))))) | (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a))))))))))))"
shows "(((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))))))))) | (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a))))))))))"(is "PROP ?ob'225")
proof -
ML_command {* writeln "*** TLAPS ENTER 225"; *}
show "PROP ?ob'225"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_0339f8.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_0339f8.znn.out
;; obligation #225
$hyp "v'51" (/\ (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_InvBunde_a)
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'52" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "v'69" (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)))
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h003cd)
$hyp "v'73" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'74" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$hyp "v'79" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'80" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'81" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'82" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'83" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$hyp "v'84" (=> (/\ (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'85" (=> (/\ (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset) (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a)))))))
$goal (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hp")
 using v'81 by blast
 have z_Hk:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hbc")
 using v'82 by blast
 have z_Hm:"(((a_VARIABLEunde_knownunde_hash_primea=?z_hp)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbc)&(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})&((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))))=>((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a])) < a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_Punde_a[a_CONSTANTunde_iunde_a]))))))|((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a]) \\subseteq UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_Punde_a[a_CONSTANTunde_iunde_a])))))))" (is "?z_hbl=>?z_hcb")
 using v'85 by blast
 have z_Hi:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hi")
 using v'79 by blast
 have z_Hl:"(((a_VARIABLEunde_knownunde_hash_primea=?z_hp)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hbc)&(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)))))=>?z_hcb)" (is "?z_hct=>_")
 using v'84 by blast
 have zenon_L1_: "(a_VARIABLEunde_knownunde_hash_primea=?z_hp) ==> (a_VARIABLEunde_knownunde_hash_primea~=?z_hp) ==> FALSE" (is "?z_hj ==> ?z_hcw ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hcw:"?z_hcw"
  show FALSE
  by (rule notE [OF z_Hcw z_Hj])
 qed
 have zenon_L2_: "(a_VARIABLEunde_notKnownunde_hash_primea=?z_hbc) ==> (a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbc) ==> FALSE" (is "?z_hk ==> ?z_hcx ==> FALSE")
 proof -
  assume z_Hk:"?z_hk"
  assume z_Hcx:"?z_hcx"
  show FALSE
  by (rule notE [OF z_Hcx z_Hk])
 qed
 have zenon_L3_: "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))) ==> (a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))) ==> FALSE" (is "?z_hbr ==> ?z_hcy ==> FALSE")
 proof -
  assume z_Hbr:"?z_hbr" (is "?z_hbs&?z_hbw")
  assume z_Hcy:"?z_hcy" (is "_~=?z_hbu")
  have z_Hbs: "?z_hbs"
  by (rule zenon_and_0 [OF z_Hbr])
  show FALSE
  by (rule notE [OF z_Hcy z_Hbs])
 qed
 have zenon_L4_: "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))) ==> (a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')) ==> FALSE" (is "?z_hbr ==> ?z_hcz ==> FALSE")
 proof -
  assume z_Hbr:"?z_hbr" (is "?z_hbs&?z_hbw")
  assume z_Hcz:"?z_hcz" (is "_~=?z_hby")
  have z_Hbw: "?z_hbw"
  by (rule zenon_and_1 [OF z_Hbr])
  show FALSE
  by (rule notE [OF z_Hcz z_Hbw])
 qed
 have zenon_L5_: "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)) ==> (a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b'')) ==> FALSE" (is "?z_hco ==> ?z_hda ==> FALSE")
 proof -
  assume z_Hco:"?z_hco" (is "?z_hcp&?z_hcs")
  assume z_Hda:"?z_hda" (is "_~=?z_hcq")
  have z_Hcp: "?z_hcp"
  by (rule zenon_and_0 [OF z_Hco])
  show FALSE
  by (rule notE [OF z_Hda z_Hcp])
 qed
 have zenon_L6_: "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)) ==> (a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hco ==> ?z_hdb ==> FALSE")
 proof -
  assume z_Hco:"?z_hco" (is "?z_hcp&?z_hcs")
  assume z_Hdb:"?z_hdb"
  have z_Hcs: "?z_hcs"
  by (rule zenon_and_1 [OF z_Hco])
  show FALSE
  by (rule notE [OF z_Hdb z_Hcs])
 qed
 assume z_Hn:"(~?z_hcb)" (is "~(?z_hcc|?z_hcm)")
 have z_Hdc: "(~?z_hcc)"
 by (rule zenon_notor_0 [OF z_Hn])
 have z_Hdd: "(~?z_hcm)"
 by (rule zenon_notor_1 [OF z_Hn])
 show FALSE
 proof (rule zenon_imply [OF z_Hl])
  assume z_Hde:"(~?z_hct)" (is "~(?z_hj&?z_hcu)")
  show FALSE
  proof (rule zenon_notand [OF z_Hde])
   assume z_Hcw:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hp)"
   show FALSE
   by (rule notE [OF z_Hcw z_Hj])
  next
   assume z_Hdf:"(~?z_hcu)" (is "~(?z_hk&?z_hcv)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdf])
    assume z_Hcx:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbc)"
    show FALSE
    by (rule notE [OF z_Hcx z_Hk])
   next
    assume z_Hdg:"(~?z_hcv)" (is "~(?z_hcn&?z_hco)")
    show FALSE
    proof (rule zenon_notand [OF z_Hdg])
     assume z_Hdh:"(~?z_hcn)" (is "~~?z_hbo")
     have z_Hbo: "?z_hbo" (is "?z_hbp=_")
     by (rule zenon_notnot_0 [OF z_Hdh])
     show FALSE
     proof (rule zenon_imply [OF z_Hm])
      assume z_Hdi:"(~?z_hbl)" (is "~(_&?z_hbm)")
      show FALSE
      proof (rule zenon_notand [OF z_Hdi])
       assume z_Hcw:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hp)"
       show FALSE
       by (rule notE [OF z_Hcw z_Hj])
      next
       assume z_Hdj:"(~?z_hbm)" (is "~(_&?z_hbn)")
       show FALSE
       proof (rule zenon_notand [OF z_Hdj])
        assume z_Hcx:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbc)"
        show FALSE
        by (rule notE [OF z_Hcx z_Hk])
       next
        assume z_Hdk:"(~?z_hbn)" (is "~(_&?z_hbr)")
        show FALSE
        proof (rule zenon_notand [OF z_Hdk])
         assume z_Hcn:"?z_hcn"
         show FALSE
         by (rule notE [OF z_Hcn z_Hbo])
        next
         assume z_Hdl:"(~?z_hbr)" (is "~(?z_hbs&?z_hbw)")
         show FALSE
         proof (rule zenon_notand [OF z_Hdl])
          assume z_Hcy:"(a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hbu")
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
           assume z_Hcn:"?z_hcn"
           assume z_Hco:"?z_hco" (is "?z_hcp&?z_hcs")
           show FALSE
           by (rule notE [OF z_Hcn z_Hbo])
          next
           assume z_Hdh:"(~?z_hcn)"
           assume z_Hbr:"?z_hbr"
           show FALSE
           by (rule zenon_L3_ [OF z_Hbr z_Hcy])
          qed
         next
          assume z_Hcz:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_~=?z_hby")
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
           assume z_Hcn:"?z_hcn"
           assume z_Hco:"?z_hco" (is "?z_hcp&?z_hcs")
           show FALSE
           by (rule notE [OF z_Hcn z_Hbo])
          next
           assume z_Hdh:"(~?z_hcn)"
           assume z_Hbr:"?z_hbr"
           show FALSE
           by (rule zenon_L4_ [OF z_Hbr z_Hcz])
          qed
         qed
        qed
       qed
      qed
     next
      assume z_Hcb:"?z_hcb"
      show FALSE
      proof (rule zenon_or [OF z_Hcb])
       assume z_Hcc:"?z_hcc"
       show FALSE
       by (rule notE [OF z_Hdc z_Hcc])
      next
       assume z_Hcm:"?z_hcm"
       show FALSE
       by (rule notE [OF z_Hdd z_Hcm])
      qed
     qed
    next
     assume z_Hdo:"(~?z_hco)" (is "~(?z_hcp&?z_hcs)")
     show FALSE
     proof (rule zenon_notand [OF z_Hdo])
      assume z_Hda:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))" (is "_~=?z_hcq")
      show FALSE
      proof (rule zenon_imply [OF z_Hm])
       assume z_Hdi:"(~?z_hbl)" (is "~(_&?z_hbm)")
       show FALSE
       proof (rule zenon_notand [OF z_Hdi])
        assume z_Hcw:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hp)"
        show FALSE
        by (rule notE [OF z_Hcw z_Hj])
       next
        assume z_Hdj:"(~?z_hbm)" (is "~(_&?z_hbn)")
        show FALSE
        proof (rule zenon_notand [OF z_Hdj])
         assume z_Hcx:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbc)"
         show FALSE
         by (rule notE [OF z_Hcx z_Hk])
        next
         assume z_Hdk:"(~?z_hbn)" (is "~(?z_hbo&?z_hbr)")
         show FALSE
         proof (rule zenon_notand [OF z_Hdk])
          assume z_Hcn:"?z_hcn" (is "?z_hbp~=_")
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
           assume z_Hcn:"?z_hcn"
           assume z_Hco:"?z_hco"
           show FALSE
           by (rule zenon_L5_ [OF z_Hco z_Hda])
          next
           assume z_Hdh:"(~?z_hcn)"
           assume z_Hbr:"?z_hbr" (is "?z_hbs&?z_hbw")
           show FALSE
           by (rule notE [OF z_Hdh z_Hcn])
          qed
         next
          assume z_Hdl:"(~?z_hbr)" (is "~(?z_hbs&?z_hbw)")
          show FALSE
          proof (rule zenon_notand [OF z_Hdl])
           assume z_Hcy:"(a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hbu")
           show FALSE
           proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
            assume z_Hcn:"?z_hcn" (is "?z_hbp~=_")
            assume z_Hco:"?z_hco"
            show FALSE
            by (rule zenon_L5_ [OF z_Hco z_Hda])
           next
            assume z_Hdh:"(~?z_hcn)"
            assume z_Hbr:"?z_hbr"
            show FALSE
            by (rule zenon_L3_ [OF z_Hbr z_Hcy])
           qed
          next
           assume z_Hcz:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_~=?z_hby")
           show FALSE
           proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
            assume z_Hcn:"?z_hcn" (is "?z_hbp~=_")
            assume z_Hco:"?z_hco"
            show FALSE
            by (rule zenon_L5_ [OF z_Hco z_Hda])
           next
            assume z_Hdh:"(~?z_hcn)"
            assume z_Hbr:"?z_hbr"
            show FALSE
            by (rule zenon_L4_ [OF z_Hbr z_Hcz])
           qed
          qed
         qed
        qed
       qed
      next
       assume z_Hcb:"?z_hcb"
       show FALSE
       proof (rule zenon_or [OF z_Hcb])
        assume z_Hcc:"?z_hcc"
        show FALSE
        by (rule notE [OF z_Hdc z_Hcc])
       next
        assume z_Hcm:"?z_hcm"
        show FALSE
        by (rule notE [OF z_Hdd z_Hcm])
       qed
      qed
     next
      assume z_Hdb:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
      show FALSE
      proof (rule zenon_imply [OF z_Hm])
       assume z_Hdi:"(~?z_hbl)" (is "~(_&?z_hbm)")
       show FALSE
       proof (rule zenon_notand [OF z_Hdi])
        assume z_Hcw:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hp)"
        show FALSE
        by (rule notE [OF z_Hcw z_Hj])
       next
        assume z_Hdj:"(~?z_hbm)" (is "~(_&?z_hbn)")
        show FALSE
        proof (rule zenon_notand [OF z_Hdj])
         assume z_Hcx:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hbc)"
         show FALSE
         by (rule notE [OF z_Hcx z_Hk])
        next
         assume z_Hdk:"(~?z_hbn)" (is "~(?z_hbo&?z_hbr)")
         show FALSE
         proof (rule zenon_notand [OF z_Hdk])
          assume z_Hcn:"?z_hcn" (is "?z_hbp~=_")
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
           assume z_Hcn:"?z_hcn"
           assume z_Hco:"?z_hco"
           show FALSE
           by (rule zenon_L6_ [OF z_Hco z_Hdb])
          next
           assume z_Hdh:"(~?z_hcn)"
           assume z_Hbr:"?z_hbr" (is "?z_hbs&?z_hbw")
           show FALSE
           by (rule notE [OF z_Hdh z_Hcn])
          qed
         next
          assume z_Hdl:"(~?z_hbr)" (is "~(?z_hbs&?z_hbw)")
          show FALSE
          proof (rule zenon_notand [OF z_Hdl])
           assume z_Hcy:"(a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hbu")
           show FALSE
           proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
            assume z_Hcn:"?z_hcn" (is "?z_hbp~=_")
            assume z_Hco:"?z_hco"
            show FALSE
            by (rule zenon_L6_ [OF z_Hco z_Hdb])
           next
            assume z_Hdh:"(~?z_hcn)"
            assume z_Hbr:"?z_hbr"
            show FALSE
            by (rule zenon_L3_ [OF z_Hbr z_Hcy])
           qed
          next
           assume z_Hcz:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_~=?z_hby")
           show FALSE
           proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcn" "?z_hco" "?z_hbr", OF z_Hi])
            assume z_Hcn:"?z_hcn" (is "?z_hbp~=_")
            assume z_Hco:"?z_hco"
            show FALSE
            by (rule zenon_L6_ [OF z_Hco z_Hdb])
           next
            assume z_Hdh:"(~?z_hcn)"
            assume z_Hbr:"?z_hbr"
            show FALSE
            by (rule zenon_L4_ [OF z_Hbr z_Hcz])
           qed
          qed
         qed
        qed
       qed
      next
       assume z_Hcb:"?z_hcb"
       show FALSE
       proof (rule zenon_or [OF z_Hcb])
        assume z_Hcc:"?z_hcc"
        show FALSE
        by (rule notE [OF z_Hdc z_Hcc])
       next
        assume z_Hcm:"?z_hcm"
        show FALSE
        by (rule notE [OF z_Hdd z_Hcm])
       qed
      qed
     qed
    qed
   qed
  qed
 next
  assume z_Hcb:"?z_hcb"
  show FALSE
  proof (rule zenon_or [OF z_Hcb])
   assume z_Hcc:"?z_hcc"
   show FALSE
   by (rule notE [OF z_Hdc z_Hcc])
  next
   assume z_Hcm:"?z_hcm"
   show FALSE
   by (rule notE [OF z_Hdd z_Hcm])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 225"; *} qed
lemma ob'196:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'49: "((((((((((a_VARIABLEunde_A1unde_a) \<in> ([(Nat) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_resultunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_pcunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ({(''a''), (''b''), (''Done'')})]))) & (((a_VARIABLEunde_knownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_notKnownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (Nat)))]))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))))))) \<and> ((\<forall> a_CONSTANTunde_iunde_a \<in> (Nat) : (((((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a))) \<noteq> ({}))) \<Rightarrow> ((geq (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))), (a_CONSTANTunde_iunde_a))))))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (\<forall> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((leq ((a_CONSTANTunde_iunde_a), ((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) & (((a_CONSTANTunde_punde_a) \<in> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Leftrightarrow> (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''Done''))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Rightarrow> (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'50: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_punde_1unde_a
assumes a_CONSTANTunde_punde_1unde_a_in : "(a_CONSTANTunde_punde_1unde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'73: "(((((a_CONSTANTunde_punde_1unde_a) = (a_CONSTANTunde_punde_a))) \<Longrightarrow> (((((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (''b''))) \<Rightarrow> (\<forall> a_CONSTANTunde_iunde_a \<in> (fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) : ((leq ((a_CONSTANTunde_iunde_a), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))))))))))))))"
assumes v'74: "(((a_CONSTANTunde_punde_1unde_a) \<noteq> (a_CONSTANTunde_punde_a)))"
assumes v'77: "((((a_CONSTANTunde_IsFiniteSetunde_a ((a_STATEunde_snapshotunde_a)))) \<and> (((a_STATEunde_snapshotunde_a) \<subseteq> (a_CONSTANTunde_Procunde_a)))))"
assumes v'78: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'79: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'80: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'81: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'82: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'83: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'84: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
shows "(((((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (''b''))) \<Rightarrow> (\<forall> a_CONSTANTunde_iunde_a \<in> (fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) : ((leq ((a_CONSTANTunde_iunde_a), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))))))))))))"(is "PROP ?ob'196")
proof -
ML_command {* writeln "*** TLAPS ENTER 196"; *}
show "PROP ?ob'196"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_cd64c8.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_cd64c8.znn.out
;; obligation #196
$hyp "v'49" (/\ (/\ (/\ (/\ (TLA.in a_VARIABLEunde_A1unde_a
(TLA.FuncSet arith.N (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_resultunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_pcunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.set "a" "b" "Done")))
(TLA.in a_VARIABLEunde_knownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_notKnownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET arith.N)))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b") (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))))))
(/\ (TLA.bAll arith.N ((a_CONSTANTunde_iunde_a) (=> (-. (= (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)
TLA.emptyset)) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a))))))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
(TLA.bAll (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))
(TLA.in a_CONSTANTunde_punde_a
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(<=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset)) (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"Done"))
(=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))
(= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))))
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'50" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_punde_1unde_a_in" (TLA.in a_CONSTANTunde_punde_1unde_a a_CONSTANTunde_Procunde_a)
$hyp "v'73" (=> (= a_CONSTANTunde_punde_1unde_a
a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_1unde_a)
"b")
(TLA.bAll (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_1unde_a) ((a_CONSTANTunde_iunde_a) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_1unde_a)))))))
$hyp "v'74" (-. (= a_CONSTANTunde_punde_1unde_a
a_CONSTANTunde_punde_a))
$hyp "v'77" (/\ (a_CONSTANTunde_IsFiniteSetunde_a a_STATEunde_snapshotunde_a)
(TLA.subseteq a_STATEunde_snapshotunde_a
a_CONSTANTunde_Procunde_a))
$hyp "v'78" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'79" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'80" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'81" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'82" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'83" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'84" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$goal (=> (= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_1unde_a)
"b")
(TLA.bAll (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_1unde_a) ((a_CONSTANTunde_iunde_a) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_1unde_a))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((((a_VARIABLEunde_A1unde_a \\in FuncSet(Nat, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_resultunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''}))&((a_VARIABLEunde_knownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_notKnownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(Nat)))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})))))))))&(bAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])~={})=>(a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. ((((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))&((a_CONSTANTunde_punde_a \\in (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))&((((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})<=>((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''Done''))&(((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})=>((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))))))&a_STATEunde_InvCunde_a)&a_STATEunde_GFXCorrectunde_a)" (is "?z_hp&_")
 using v'49 by blast
 have z_Hl:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hdf")
 using v'82 by blast
 have z_Hm:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hdl")
 using v'83 by blast
 have z_Hf:"(a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a)"
 using v'74 by blast
 have z_Hd:"(a_CONSTANTunde_punde_1unde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hd")
 using a_CONSTANTunde_punde_1unde_a_in by blast
 have z_Hj:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hj")
 using v'80 by blast
 have zenon_L1_: "(\\A zenon_Vld:((zenon_Vld \\in DOMAIN(a_VARIABLEunde_pcunde_a))<=>(zenon_Vld \\in a_CONSTANTunde_Procunde_a))) ==> ?z_hd ==> (~(a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_pcunde_a))) ==> FALSE" (is "?z_heh ==> _ ==> ?z_hen ==> FALSE")
 proof -
  assume z_Heh:"?z_heh" (is "\\A x : ?z_hep(x)")
  assume z_Hd:"?z_hd"
  assume z_Hen:"?z_hen" (is "~?z_heo")
  have z_Heq: "?z_hep(a_CONSTANTunde_punde_1unde_a)"
  by (rule zenon_all_0 [of "?z_hep" "a_CONSTANTunde_punde_1unde_a", OF z_Heh])
  show FALSE
  proof (rule zenon_equiv [OF z_Heq])
   assume z_Hen:"?z_hen"
   assume z_Her:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Her z_Hd])
  next
   assume z_Heo:"?z_heo"
   assume z_Hd:"?z_hd"
   show FALSE
   by (rule notE [OF z_Hen z_Heo])
  qed
 qed
 have zenon_L2_: "(DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a) ==> ?z_hd ==> ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=(a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])) ==> (a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a) ==> (a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b'')) ==> FALSE" (is "?z_hes ==> _ ==> ?z_het ==> ?z_hf ==> ?z_hdx ==> FALSE")
 proof -
  assume z_Hes:"?z_hes" (is "?z_hel=_")
  assume z_Hd:"?z_hd"
  assume z_Het:"?z_het" (is "?z_heu~=?z_hev")
  assume z_Hf:"?z_hf"
  assume z_Hdx:"?z_hdx" (is "_=?z_hdz")
  have z_Heh: "(\\A zenon_Vld:((zenon_Vld \\in ?z_hel)<=>(zenon_Vld \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hep(x)")
  by (rule zenon_setequal_0 [of "?z_hel" "a_CONSTANTunde_Procunde_a", OF z_Hes])
  have z_Hew: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_hdz))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_hdz)))&(\\A zenon_Veel:((a_VARIABLEunde_pcunde_hash_primea[zenon_Veel])=(?z_hdz[zenon_Veel]))))" (is "?z_hex&?z_hfe")
  by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_hdz", OF z_Hdx])
  have z_Hfe: "?z_hfe" (is "\\A x : ?z_hfj(x)")
  by (rule zenon_and_1 [OF z_Hew])
  have z_Hfk: "?z_hfj(a_CONSTANTunde_punde_1unde_a)" (is "_=?z_hfl")
  by (rule zenon_all_0 [of "?z_hfj" "a_CONSTANTunde_punde_1unde_a", OF z_Hfe])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vmrj. (?z_hev=zenon_Vmrj))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "''b''" "a_CONSTANTunde_punde_1unde_a", OF z_Hfk])
   assume z_Heo:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hel)" (is "?z_heo")
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfq:"(?z_hev=''b'')" (is "_=?z_hbi")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Heo:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hel)" (is "?z_heo")
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfs:"(?z_hev=?z_heu)"
   show FALSE
   by (rule zenon_eqsym [OF z_Hfs z_Het])
  next
   assume z_Hen:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hel))" (is "~?z_heo")
   show FALSE
   by (rule zenon_L1_ [OF z_Heh z_Hd z_Hen])
  qed
 qed
 have zenon_L3_: "bAll((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_1unde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))))) ==> (~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a])))) ==> ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_1unde_a])) ==> FALSE" (is "?z_hft ==> ?z_hfz ==> ?z_hgk ==> FALSE")
 proof -
  assume z_Hft:"?z_hft"
  assume z_Hfz:"?z_hfz" (is "~?z_hga")
  assume z_Hgk:"?z_hgk"
  have z_Hgl_z_Hft: "(\\A x:((x \\in (a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))))) == ?z_hft" (is "?z_hgl == _")
  by (unfold bAll_def)
  have z_Hgl: "?z_hgl" (is "\\A x : ?z_hgp(x)")
  by (unfold z_Hgl_z_Hft, fact z_Hft)
  have z_Hgq: "?z_hgp((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))))"
  by (rule zenon_all_0 [of "?z_hgp" "(CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))))))", OF z_Hgl])
  show FALSE
  proof (rule zenon_imply [OF z_Hgq])
   assume z_Hgr:"(~?z_hgk)"
   show FALSE
   by (rule notE [OF z_Hgr z_Hgk])
  next
   assume z_Hga:"?z_hga"
   show FALSE
   by (rule notE [OF z_Hfz z_Hga])
  qed
 qed
 have zenon_L4_: "(~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((?z_hdf[a_CONSTANTunde_punde_1unde_a])))) ==> (a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> (\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) ==> ?z_hd ==> ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])=''b'') ==> (a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b'')) ==> (DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a) ==> (a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_notKnownunde_a)) ==> ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a])) ==> (a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a) ==> FALSE" (is "?z_hgs ==> ?z_hgw ==> ?z_hgy ==> _ ==> ?z_hfq ==> ?z_hdx ==> ?z_hes ==> ?z_hhu ==> ?z_hhw ==> ?z_hf ==> FALSE")
 proof -
  assume z_Hgs:"?z_hgs" (is "~?z_hgt")
  assume z_Hgw:"?z_hgw"
  assume z_Hgy:"?z_hgy" (is "\\A x : ?z_hhy(x)")
  assume z_Hd:"?z_hd"
  assume z_Hfq:"?z_hfq" (is "?z_hev=?z_hbi")
  assume z_Hdx:"?z_hdx" (is "_=?z_hdz")
  assume z_Hes:"?z_hes" (is "?z_hel=_")
  assume z_Hhu:"?z_hhu"
  assume z_Hhw:"?z_hhw"
  assume z_Hf:"?z_hf"
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vcb. (~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(zenon_Vcb))))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hgs])
   assume z_Hgw:"?z_hgw"
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hie:"(~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))))" (is "~?z_hif")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Hgw:"?z_hgw"
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfz:"(~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))))" (is "~?z_hga")
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Veb. ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in zenon_Veb))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hhw])
    assume z_Hhu:"?z_hhu"
    assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
    assume z_Hik:"((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" (is "?z_hik")
    show FALSE
    by (rule zenon_eqsym [OF z_Hfp z_Hf])
   next
    assume z_Hhu:"?z_hhu"
    assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
    assume z_Hgk:"((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "?z_hgk")
    have z_Hil: "?z_hhy(a_CONSTANTunde_punde_1unde_a)" (is "_=>?z_him")
    by (rule zenon_all_0 [of "?z_hhy" "a_CONSTANTunde_punde_1unde_a", OF z_Hgy])
    show FALSE
    proof (rule zenon_imply [OF z_Hil])
     assume z_Her:"(~?z_hd)"
     show FALSE
     by (rule notE [OF z_Her z_Hd])
    next
     assume z_Him:"?z_him" (is "?z_hin&?z_hio")
     have z_Hin: "?z_hin" (is "?z_hip=>?z_hft")
     by (rule zenon_and_0 [OF z_Him])
     show FALSE
     proof (rule zenon_imply [OF z_Hin])
      assume z_Hiq:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=?z_hbi)" (is "?z_heu~=_")
      show FALSE
      proof (rule notE [OF z_Hiq])
       have z_Hfs: "(?z_hev=?z_heu)"
       proof (rule zenon_nnpp [of "(?z_hev=?z_heu)"])
        assume z_Hir:"(?z_hev~=?z_heu)"
        show FALSE
        proof (rule zenon_em [of "(?z_heu=?z_heu)"])
         assume z_His:"(?z_heu=?z_heu)"
         show FALSE
         proof (rule notE [OF z_Hir])
          have z_Hit: "(?z_heu=?z_hev)"
          proof (rule zenon_nnpp [of "(?z_heu=?z_hev)"])
           assume z_Het:"(?z_heu~=?z_hev)"
           show FALSE
           by (rule zenon_L2_ [OF z_Hes z_Hd z_Het z_Hf z_Hdx])
          qed
          have z_Hfs: "(?z_hev=?z_heu)"
          by (rule subst [where P="(\<lambda>zenon_Vycr. (zenon_Vycr=?z_heu))", OF z_Hit], fact z_His)
          thus "(?z_hev=?z_heu)" .
         qed
        next
         assume z_Hix:"(?z_heu~=?z_heu)"
         show FALSE
         by (rule zenon_noteq [OF z_Hix])
        qed
       qed
       have z_Hip: "?z_hip"
       by (rule subst [where P="(\<lambda>zenon_Vzcr. (zenon_Vzcr=?z_hbi))", OF z_Hfs], fact z_Hfq)
       thus "?z_hip" .
      qed
     next
      assume z_Hft:"?z_hft"
      show FALSE
      by (rule zenon_L3_ [OF z_Hft z_Hfz z_Hgk])
     qed
    qed
   next
    assume z_Hjb:"(~?z_hhu)"
    show FALSE
    by (rule notE [OF z_Hjb z_Hhu])
   qed
  next
   assume z_Hjc:"(~?z_hgw)"
   show FALSE
   by (rule notE [OF z_Hjc z_Hgw])
  qed
 qed
 have zenon_L5_: "(DOMAIN(a_VARIABLEunde_knownunde_a)~=DOMAIN(a_VARIABLEunde_notKnownunde_a)) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> FALSE" (is "?z_hjd ==> ?z_hje ==> ?z_hjf ==> FALSE")
 proof -
  assume z_Hjd:"?z_hjd" (is "?z_hgx~=?z_hhv")
  assume z_Hje:"?z_hje"
  assume z_Hjf:"?z_hjf"
  show FALSE
  proof (rule notE [OF z_Hjd])
   have z_Hjg: "(a_CONSTANTunde_Procunde_a=?z_hhv)"
   by (rule sym [OF z_Hjf])
   have z_Hjh: "(?z_hgx=?z_hhv)"
   by (rule subst [where P="(\<lambda>zenon_Vadr. (?z_hgx=zenon_Vadr))", OF z_Hjg], fact z_Hje)
   thus "(?z_hgx=?z_hhv)" .
  qed
 qed
 have zenon_L6_: "(~(a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_notKnownunde_a))) ==> (a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> FALSE" (is "?z_hjb ==> ?z_hgw ==> ?z_hjf ==> ?z_hje ==> FALSE")
 proof -
  assume z_Hjb:"?z_hjb" (is "~?z_hhu")
  assume z_Hgw:"?z_hgw"
  assume z_Hjf:"?z_hjf" (is "?z_hhv=_")
  assume z_Hje:"?z_hje" (is "?z_hgx=_")
  show FALSE
  proof (rule notE [OF z_Hjb])
   have z_Hjh: "(?z_hgx=?z_hhv)"
   proof (rule zenon_nnpp [of "(?z_hgx=?z_hhv)"])
    assume z_Hjd:"(?z_hgx~=?z_hhv)"
    show FALSE
    by (rule zenon_L5_ [OF z_Hjd z_Hje z_Hjf])
   qed
   have z_Hhu: "?z_hhu"
   by (rule subst [where P="(\<lambda>zenon_Vgar. (a_CONSTANTunde_punde_1unde_a \\in zenon_Vgar))", OF z_Hjh], fact z_Hgw)
   thus "?z_hhu" .
  qed
 qed
 have zenon_L7_: "((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a])) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a])) ==> (DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a) ==> (a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b'')) ==> ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])=''b'') ==> ?z_hd ==> (\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) ==> (a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> (~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((?z_hdf[a_CONSTANTunde_punde_1unde_a])))) ==> (a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a) ==> FALSE" (is "?z_hjo ==> ?z_hje ==> ?z_hjf ==> ?z_hhw ==> ?z_hes ==> ?z_hdx ==> ?z_hfq ==> _ ==> ?z_hgy ==> ?z_hgw ==> ?z_hgs ==> ?z_hf ==> FALSE")
 proof -
  assume z_Hjo:"?z_hjo"
  assume z_Hje:"?z_hje" (is "?z_hgx=_")
  assume z_Hjf:"?z_hjf" (is "?z_hhv=_")
  assume z_Hhw:"?z_hhw"
  assume z_Hes:"?z_hes" (is "?z_hel=_")
  assume z_Hdx:"?z_hdx" (is "_=?z_hdz")
  assume z_Hfq:"?z_hfq" (is "?z_hev=?z_hbi")
  assume z_Hd:"?z_hd"
  assume z_Hgy:"?z_hgy" (is "\\A x : ?z_hhy(x)")
  assume z_Hgw:"?z_hgw"
  assume z_Hgs:"?z_hgs" (is "~?z_hgt")
  assume z_Hf:"?z_hf"
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vob. ((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in zenon_Vob))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hjo])
   assume z_Hhu:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hhv)" (is "?z_hhu")
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hjw:"((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" (is "?z_hjw")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Hhu:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hhv)" (is "?z_hhu")
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hjx:"((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "?z_hjx")
   show FALSE
   by (rule zenon_L4_ [OF z_Hgs z_Hgw z_Hgy z_Hd z_Hfq z_Hdx z_Hes z_Hhu z_Hhw z_Hf])
  next
   assume z_Hjb:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hhv))" (is "~?z_hhu")
   show FALSE
   by (rule zenon_L6_ [OF z_Hjb z_Hgw z_Hjf z_Hje])
  qed
 qed
 have zenon_L8_: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (~(a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a))) ==> ?z_hd ==> FALSE" (is "?z_hje ==> ?z_hjc ==> _ ==> FALSE")
 proof -
  assume z_Hje:"?z_hje" (is "?z_hgx=_")
  assume z_Hjc:"?z_hjc" (is "~?z_hgw")
  assume z_Hd:"?z_hd"
  have z_Hjy: "(\\A zenon_Vqd:((zenon_Vqd \\in ?z_hgx)<=>(zenon_Vqd \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hkd(x)")
  by (rule zenon_setequal_0 [of "?z_hgx" "a_CONSTANTunde_Procunde_a", OF z_Hje])
  have z_Hke: "?z_hkd(a_CONSTANTunde_punde_1unde_a)"
  by (rule zenon_all_0 [of "?z_hkd" "a_CONSTANTunde_punde_1unde_a", OF z_Hjy])
  show FALSE
  proof (rule zenon_equiv [OF z_Hke])
   assume z_Hjc:"?z_hjc"
   assume z_Her:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Her z_Hd])
  next
   assume z_Hgw:"?z_hgw"
   assume z_Hd:"?z_hd"
   show FALSE
   by (rule notE [OF z_Hjc z_Hgw])
  qed
 qed
 have zenon_L9_: "(DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a) ==> ?z_hd ==> ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=(a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])) ==> (a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a) ==> (a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')) ==> FALSE" (is "?z_hes ==> _ ==> ?z_het ==> ?z_hf ==> ?z_hef ==> FALSE")
 proof -
  assume z_Hes:"?z_hes" (is "?z_hel=_")
  assume z_Hd:"?z_hd"
  assume z_Het:"?z_het" (is "?z_heu~=?z_hev")
  assume z_Hf:"?z_hf"
  assume z_Hef:"?z_hef" (is "_=?z_heg")
  have z_Heh: "(\\A zenon_Vld:((zenon_Vld \\in ?z_hel)<=>(zenon_Vld \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hep(x)")
  by (rule zenon_setequal_0 [of "?z_hel" "a_CONSTANTunde_Procunde_a", OF z_Hes])
  have z_Hkf: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_heg))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_heg)))&(\\A zenon_Voe:((a_VARIABLEunde_pcunde_hash_primea[zenon_Voe])=(?z_heg[zenon_Voe]))))" (is "?z_hkg&?z_hkl")
  by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_heg", OF z_Hef])
  have z_Hkl: "?z_hkl" (is "\\A x : ?z_hkq(x)")
  by (rule zenon_and_1 [OF z_Hkf])
  have z_Hkr: "?z_hkq(a_CONSTANTunde_punde_1unde_a)" (is "_=?z_hks")
  by (rule zenon_all_0 [of "?z_hkq" "a_CONSTANTunde_punde_1unde_a", OF z_Hkl])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vmrj. (?z_hev=zenon_Vmrj))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "''Done''" "a_CONSTANTunde_punde_1unde_a", OF z_Hkr])
   assume z_Heo:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hel)" (is "?z_heo")
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hkt:"(?z_hev=''Done'')" (is "_=?z_hbj")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Heo:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hel)" (is "?z_heo")
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfs:"(?z_hev=?z_heu)"
   show FALSE
   by (rule zenon_eqsym [OF z_Hfs z_Het])
  next
   assume z_Hen:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hel))" (is "~?z_heo")
   show FALSE
   by (rule zenon_L1_ [OF z_Heh z_Hd z_Hen])
  qed
 qed
 have zenon_L10_: "(~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((?z_hdf[a_CONSTANTunde_punde_1unde_a])))) ==> (a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> (\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) ==> ?z_hd ==> (DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a) ==> (a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')) ==> ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])=''b'') ==> (a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''})) ==> (a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_notKnownunde_a)) ==> ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a])) ==> (a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a) ==> FALSE" (is "?z_hgs ==> ?z_hgw ==> ?z_hgy ==> _ ==> ?z_hes ==> ?z_hef ==> ?z_hfq ==> ?z_hbd ==> ?z_hhu ==> ?z_hhw ==> ?z_hf ==> FALSE")
 proof -
  assume z_Hgs:"?z_hgs" (is "~?z_hgt")
  assume z_Hgw:"?z_hgw"
  assume z_Hgy:"?z_hgy" (is "\\A x : ?z_hhy(x)")
  assume z_Hd:"?z_hd"
  assume z_Hes:"?z_hes" (is "?z_hel=_")
  assume z_Hef:"?z_hef" (is "_=?z_heg")
  assume z_Hfq:"?z_hfq" (is "?z_hev=?z_hbi")
  assume z_Hbd:"?z_hbd"
  assume z_Hhu:"?z_hhu"
  assume z_Hhw:"?z_hhw"
  assume z_Hf:"?z_hf"
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vcb. (~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(zenon_Vcb))))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hgs])
   assume z_Hgw:"?z_hgw"
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hie:"(~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))))" (is "~?z_hif")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Hgw:"?z_hgw"
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfz:"(~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))))" (is "~?z_hga")
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Veb. ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in zenon_Veb))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hhw])
    assume z_Hhu:"?z_hhu"
    assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
    assume z_Hik:"((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" (is "?z_hik")
    show FALSE
    by (rule zenon_eqsym [OF z_Hfp z_Hf])
   next
    assume z_Hhu:"?z_hhu"
    assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
    assume z_Hgk:"((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "?z_hgk")
    have z_Hil: "?z_hhy(a_CONSTANTunde_punde_1unde_a)" (is "_=>?z_him")
    by (rule zenon_all_0 [of "?z_hhy" "a_CONSTANTunde_punde_1unde_a", OF z_Hgy])
    show FALSE
    proof (rule zenon_imply [OF z_Hil])
     assume z_Her:"(~?z_hd)"
     show FALSE
     by (rule notE [OF z_Her z_Hd])
    next
     assume z_Him:"?z_him" (is "?z_hin&?z_hio")
     have z_Hin: "?z_hin" (is "?z_hip=>?z_hft")
     by (rule zenon_and_0 [OF z_Him])
     have z_Hio: "?z_hio" (is "?z_hku&?z_hkv")
     by (rule zenon_and_1 [OF z_Him])
     have z_Hkv: "?z_hkv" (is "?z_hkw&?z_hkx")
     by (rule zenon_and_1 [OF z_Hio])
     have z_Hkw: "?z_hkw" (is "?z_hky<=>?z_hkz")
     by (rule zenon_and_0 [OF z_Hkv])
     show FALSE
     proof (rule zenon_imply [OF z_Hin])
      assume z_Hiq:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=?z_hbi)" (is "?z_heu~=_")
      show FALSE
      proof (rule zenon_equiv [OF z_Hkw])
       assume z_Hla:"(~?z_hky)" (is "~~?z_hlb")
       assume z_Hlc:"(?z_heu~=''Done'')" (is "_~=?z_hbj")
       have z_Hes: "?z_hes"
       by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_Procunde_a" "{''a'', ?z_hbi, ?z_hbj}", OF z_Hbd])
       have z_Hld: "(\\A zenon_Vga:((zenon_Vga \\in a_CONSTANTunde_Procunde_a)=>((a_VARIABLEunde_pcunde_a[zenon_Vga]) \\in {''a'', ?z_hbi, ?z_hbj})))" (is "\\A x : ?z_hlj(x)")
       by (rule zenon_in_funcset_2 [of "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_Procunde_a" "{''a'', ?z_hbi, ?z_hbj}", OF z_Hbd])
       have z_Hlk: "?z_hlj(a_CONSTANTunde_punde_1unde_a)" (is "_=>?z_hll")
       by (rule zenon_all_0 [of "?z_hlj" "a_CONSTANTunde_punde_1unde_a", OF z_Hld])
       show FALSE
       proof (rule zenon_imply [OF z_Hlk])
        assume z_Her:"(~?z_hd)"
        show FALSE
        by (rule notE [OF z_Her z_Hd])
       next
        assume z_Hll:"?z_hll"
        show FALSE
        proof (rule zenon_in_addElt [of "?z_heu" "''a''" "{?z_hbi, ?z_hbj}", OF z_Hll])
         assume z_Hln:"(?z_heu=''a'')" (is "_=?z_hbh")
         have z_Hlo: "(?z_hbh~=?z_hbi)"
         by auto
         have z_Het: "(?z_heu~=?z_hev)"
         by (rule zenon_stringdiffll [OF z_Hlo z_Hln z_Hfq])
          show FALSE
          by (rule zenon_L9_ [OF z_Hes z_Hd z_Het z_Hf z_Hef])
        next
         assume z_Hlp:"(?z_heu \\in {?z_hbi, ?z_hbj})" (is "?z_hlp")
         show FALSE
         proof (rule zenon_in_addElt [of "?z_heu" "?z_hbi" "{?z_hbj}", OF z_Hlp])
          assume z_Hip:"?z_hip"
          show FALSE
          by (rule notE [OF z_Hiq z_Hip])
         next
          assume z_Hlr:"(?z_heu \\in {?z_hbj})" (is "?z_hlr")
          show FALSE
          proof (rule zenon_in_addElt [of "?z_heu" "?z_hbj" "{}", OF z_Hlr])
           assume z_Hkz:"?z_hkz"
           show FALSE
           by (rule notE [OF z_Hlc z_Hkz])
          next
           assume z_Hlt:"(?z_heu \\in {})" (is "?z_hlt")
           show FALSE
           by (rule zenon_in_emptyset [of "?z_heu", OF z_Hlt])
          qed
         qed
        qed
       qed
      next
       assume z_Hky:"?z_hky" (is "?z_hlu~=_")
       assume z_Hkz:"?z_hkz" (is "_=?z_hbj")
       have z_Hlv: "(?z_hbj~=?z_hbi)"
       by auto
       have z_Het: "(?z_heu~=?z_hev)"
       by (rule zenon_stringdiffll [OF z_Hlv z_Hkz z_Hfq])
        show FALSE
        by (rule zenon_L9_ [OF z_Hes z_Hd z_Het z_Hf z_Hef])
      qed
     next
      assume z_Hft:"?z_hft"
      show FALSE
      by (rule zenon_L3_ [OF z_Hft z_Hfz z_Hgk])
     qed
    qed
   next
    assume z_Hjb:"(~?z_hhu)"
    show FALSE
    by (rule notE [OF z_Hjb z_Hhu])
   qed
  next
   assume z_Hjc:"(~?z_hgw)"
   show FALSE
   by (rule notE [OF z_Hjc z_Hgw])
  qed
 qed
 have zenon_L11_: "((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a])) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a])) ==> (a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''})) ==> ((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])=''b'') ==> (a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')) ==> (DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a) ==> ?z_hd ==> (\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) ==> (a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> (~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((?z_hdf[a_CONSTANTunde_punde_1unde_a])))) ==> (a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a) ==> FALSE" (is "?z_hjo ==> ?z_hje ==> ?z_hjf ==> ?z_hhw ==> ?z_hbd ==> ?z_hfq ==> ?z_hef ==> ?z_hes ==> _ ==> ?z_hgy ==> ?z_hgw ==> ?z_hgs ==> ?z_hf ==> FALSE")
 proof -
  assume z_Hjo:"?z_hjo"
  assume z_Hje:"?z_hje" (is "?z_hgx=_")
  assume z_Hjf:"?z_hjf" (is "?z_hhv=_")
  assume z_Hhw:"?z_hhw"
  assume z_Hbd:"?z_hbd"
  assume z_Hfq:"?z_hfq" (is "?z_hev=?z_hbi")
  assume z_Hef:"?z_hef" (is "_=?z_heg")
  assume z_Hes:"?z_hes" (is "?z_hel=_")
  assume z_Hd:"?z_hd"
  assume z_Hgy:"?z_hgy" (is "\\A x : ?z_hhy(x)")
  assume z_Hgw:"?z_hgw"
  assume z_Hgs:"?z_hgs" (is "~?z_hgt")
  assume z_Hf:"?z_hf"
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vob. ((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in zenon_Vob))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hjo])
   assume z_Hhu:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hhv)" (is "?z_hhu")
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hjw:"((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" (is "?z_hjw")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Hhu:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hhv)" (is "?z_hhu")
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hjx:"((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "?z_hjx")
   show FALSE
   by (rule zenon_L10_ [OF z_Hgs z_Hgw z_Hgy z_Hd z_Hes z_Hef z_Hfq z_Hbd z_Hhu z_Hhw z_Hf])
  next
   assume z_Hjb:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hhv))" (is "~?z_hhu")
   show FALSE
   by (rule zenon_L6_ [OF z_Hjb z_Hgw z_Hjf z_Hje])
  qed
 qed
 assume z_Ho:"(~(((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))))" (is "~(?z_hfq=>?z_hlx)")
 have z_Hp: "?z_hp" (is "?z_hq&_")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hq: "?z_hq" (is "?z_hr&?z_hcb")
 by (rule zenon_and_0 [OF z_Hp])
 have z_Hr: "?z_hr" (is "?z_hs&?z_hy")
 by (rule zenon_and_0 [OF z_Hq])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hck")
 by (rule zenon_and_1 [OF z_Hq])
 have z_Hck: "?z_hck"
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hy: "?z_hy" (is "?z_hz&?z_hbc")
 by (rule zenon_and_1 [OF z_Hr])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbk")
 by (rule zenon_and_1 [OF z_Hy])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Hbc])
 have z_Hbk: "?z_hbk" (is "?z_hbl&?z_hbn")
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hbl: "?z_hbl"
 by (rule zenon_and_0 [OF z_Hbk])
 have z_Hbn: "?z_hbn" (is "?z_hbo&?z_hbs")
 by (rule zenon_and_1 [OF z_Hbk])
 have z_Hbo: "?z_hbo"
 by (rule zenon_and_0 [OF z_Hbn])
 have z_Hgy_z_Hck: "(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) == ?z_hck" (is "?z_hgy == _")
 by (unfold bAll_def)
 have z_Hgy: "?z_hgy" (is "\\A x : ?z_hhy(x)")
 by (unfold z_Hgy_z_Hck, fact z_Hck)
 have z_Hfq: "?z_hfq" (is "?z_hev=?z_hbi")
 by (rule zenon_notimply_0 [OF z_Ho])
 have z_Hma: "(~?z_hlx)"
 by (rule zenon_notimply_1 [OF z_Ho])
 have z_Hmb_z_Hma: "(~(\\A x:((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) == (~?z_hlx)" (is "?z_hmb == ?z_hma")
 by (unfold bAll_def)
 have z_Hmb: "?z_hmb" (is "~(\\A x : ?z_hmd(x))")
 by (unfold z_Hmb_z_Hma, fact z_Hma)
 have z_Hme: "(\\E x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))))))" (is "\\E x : ?z_hmf(x)")
 by (rule zenon_notallex_0 [of "?z_hmd", OF z_Hmb])
 have z_Hmg: "?z_hmf((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))))" (is "~(?z_hmh=>?z_hmi)")
 by (rule zenon_ex_choose_0 [of "?z_hmf", OF z_Hme])
 have z_Hmh: "?z_hmh"
 by (rule zenon_notimply_0 [OF z_Hmg])
 have z_Hmj: "(~?z_hmi)"
 by (rule zenon_notimply_1 [OF z_Hmg])
 have z_Hhw: "((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))" (is "?z_hhw")
 by (rule subst [where P="(\<lambda>zenon_Vrcr. ((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) \\in (zenon_Vrcr[a_CONSTANTunde_punde_1unde_a])))", OF z_Hm z_Hmh])
 have z_Hgs: "(~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((?z_hdf[a_CONSTANTunde_punde_1unde_a]))))" (is "~?z_hgt")
 by (rule subst [where P="(\<lambda>zenon_Vtcr. (~((CHOOSE x:(~((x \\in (a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((zenon_Vtcr[a_CONSTANTunde_punde_1unde_a])))))", OF z_Hl z_Hmj])
 have z_Hmu: "(~bAll((?z_hdl[a_CONSTANTunde_punde_1unde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))))))" (is "~?z_hmv")
 by (rule subst [where P="(\<lambda>zenon_Vvcr. (~bAll((zenon_Vvcr[a_CONSTANTunde_punde_1unde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))))", OF z_Hm z_Hma])
 have z_Hnb_z_Hmu: "(~(\\A x:((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) == (~?z_hmv)" (is "?z_hnb == ?z_hmu")
 by (unfold bAll_def)
 have z_Hnb: "?z_hnb" (is "~(\\A x : ?z_hnd(x))")
 by (unfold z_Hnb_z_Hmu, fact z_Hmu)
 have z_Hne: "(\\E x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))))))" (is "\\E x : ?z_hnf(x)")
 by (rule zenon_notallex_0 [of "?z_hnd", OF z_Hnb])
 have z_Hng: "?z_hnf((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))))" (is "~(?z_hjo=>?z_hnh)")
 by (rule zenon_ex_choose_0 [of "?z_hnf", OF z_Hne])
 have z_Hjo: "?z_hjo"
 by (rule zenon_notimply_0 [OF z_Hng])
 have z_Hni: "(~?z_hnh)"
 by (rule zenon_notimply_1 [OF z_Hng])
 have z_Hnj: "(~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((?z_hdf[a_CONSTANTunde_punde_1unde_a]))))" (is "~?z_hnk")
 by (rule subst [where P="(\<lambda>zenon_Vear. (~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((zenon_Vear[a_CONSTANTunde_punde_1unde_a])))))", OF z_Hl z_Hni])
 have z_Hes: "(DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hel=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_Procunde_a" "{''a'', ?z_hbi, ''Done''}", OF z_Hbd])
 have z_Hje: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hgx=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hbl])
 have z_Hjf: "(DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hhv=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(Nat)", OF z_Hbo])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ?z_hbi))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hj])
  assume z_Hdu:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hdv~=_")
  assume z_Hdw:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ?z_hbi))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hdx&?z_hea")
  have z_Hdx: "?z_hdx" (is "_=?z_hdz")
  by (rule zenon_and_0 [OF z_Hdw])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vmb. (~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(zenon_Vmb))))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hnj])
   assume z_Hgw:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hgx)" (is "?z_hgw")
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hny:"(~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))))" (is "~?z_hnz")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Hgw:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hgx)" (is "?z_hgw")
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hoa:"(~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))))" (is "~?z_hob")
   show FALSE
   by (rule zenon_L7_ [OF z_Hjo z_Hje z_Hjf z_Hhw z_Hes z_Hdx z_Hfq z_Hd z_Hgy z_Hgw z_Hgs z_Hf])
  next
   assume z_Hjc:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hgx))" (is "~?z_hgw")
   show FALSE
   by (rule zenon_L8_ [OF z_Hje z_Hjc z_Hd])
  qed
 next
  assume z_Hoc:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hod")
  assume z_Hec:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hed&?z_hef")
  have z_Hef: "?z_hef" (is "_=?z_heg")
  by (rule zenon_and_1 [OF z_Hec])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vmb. (~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(zenon_Vmb))))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hnj])
   assume z_Hgw:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hgx)" (is "?z_hgw")
   assume z_Hfp:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hny:"(~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a(((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))))" (is "~?z_hnz")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfp z_Hf])
  next
   assume z_Hgw:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hgx)" (is "?z_hgw")
   assume z_Hfr:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hoa:"(~((CHOOSE x:(~((x \\in (?z_hdl[a_CONSTANTunde_punde_1unde_a]))=>(x <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a])))))) <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))))" (is "~?z_hob")
   show FALSE
   by (rule zenon_L11_ [OF z_Hjo z_Hje z_Hjf z_Hhw z_Hbd z_Hfq z_Hef z_Hes z_Hd z_Hgy z_Hgw z_Hgs z_Hf])
  next
   assume z_Hjc:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hgx))" (is "~?z_hgw")
   show FALSE
   by (rule zenon_L8_ [OF z_Hje z_Hjc z_Hd])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 196"; *} qed
lemma ob'218:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'49: "((((((((((a_VARIABLEunde_A1unde_a) \<in> ([(Nat) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_resultunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_pcunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ({(''a''), (''b''), (''Done'')})]))) & (((a_VARIABLEunde_knownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_notKnownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (Nat)))]))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))))))) \<and> ((\<forall> a_CONSTANTunde_iunde_a \<in> (Nat) : (((((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a))) \<noteq> ({}))) \<Rightarrow> ((geq (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))), (a_CONSTANTunde_iunde_a))))))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (\<forall> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((leq ((a_CONSTANTunde_iunde_a), ((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) & (((a_CONSTANTunde_punde_a) \<in> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Leftrightarrow> (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''Done''))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Rightarrow> (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'50: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_punde_1unde_a
assumes a_CONSTANTunde_punde_1unde_a_in : "(a_CONSTANTunde_punde_1unde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'75: "(((((a_CONSTANTunde_punde_1unde_a) = (a_CONSTANTunde_punde_a))) \<Longrightarrow> (((((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) \<noteq> ({}))) \<Leftrightarrow> (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (''Done'')))))))"
assumes v'76: "(((a_CONSTANTunde_punde_1unde_a) \<noteq> (a_CONSTANTunde_punde_a)))"
assumes v'79: "((((a_CONSTANTunde_IsFiniteSetunde_a ((a_STATEunde_snapshotunde_a)))) \<and> (((a_STATEunde_snapshotunde_a) \<subseteq> (a_CONSTANTunde_Procunde_a)))))"
assumes v'80: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'81: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'82: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'83: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'84: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'85: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'86: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
shows "(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_1unde_a)))))"(is "PROP ?ob'218")
proof -
ML_command {* writeln "*** TLAPS ENTER 218"; *}
show "PROP ?ob'218"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_714fd5.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_714fd5.znn.out
;; obligation #218
$hyp "v'49" (/\ (/\ (/\ (/\ (TLA.in a_VARIABLEunde_A1unde_a
(TLA.FuncSet arith.N (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_resultunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_pcunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.set "a" "b" "Done")))
(TLA.in a_VARIABLEunde_knownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_notKnownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET arith.N)))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b") (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))))))
(/\ (TLA.bAll arith.N ((a_CONSTANTunde_iunde_a) (=> (-. (= (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)
TLA.emptyset)) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a))))))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
(TLA.bAll (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))
(TLA.in a_CONSTANTunde_punde_a
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(<=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset)) (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"Done"))
(=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))
(= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))))
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'50" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_punde_1unde_a_in" (TLA.in a_CONSTANTunde_punde_1unde_a a_CONSTANTunde_Procunde_a)
$hyp "v'75" (=> (= a_CONSTANTunde_punde_1unde_a
a_CONSTANTunde_punde_a) (<=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_1unde_a)
TLA.emptyset))
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_1unde_a)
"Done")))
$hyp "v'76" (-. (= a_CONSTANTunde_punde_1unde_a
a_CONSTANTunde_punde_a))
$hyp "v'79" (/\ (a_CONSTANTunde_IsFiniteSetunde_a a_STATEunde_snapshotunde_a)
(TLA.subseteq a_STATEunde_snapshotunde_a
a_CONSTANTunde_Procunde_a))
$hyp "v'80" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'81" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'82" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'83" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'84" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'85" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'86" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$goal (= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_1unde_a)
(TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_1unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((((a_VARIABLEunde_A1unde_a \\in FuncSet(Nat, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_resultunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''}))&((a_VARIABLEunde_knownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_notKnownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(Nat)))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})))))))))&(bAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])~={})=>(a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. ((((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))&((a_CONSTANTunde_punde_a \\in (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))&((((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})<=>((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''Done''))&(((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})=>((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))))))&a_STATEunde_InvCunde_a)&a_STATEunde_GFXCorrectunde_a)" (is "?z_hp&_")
 using v'49 by blast
 have z_Hf:"(a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a)"
 using v'76 by blast
 have z_Hd:"(a_CONSTANTunde_punde_1unde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hd")
 using a_CONSTANTunde_punde_1unde_a_in by blast
 have z_Hj:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hj")
 using v'82 by blast
 have zenon_L1_: "(\\A zenon_Vqc:((zenon_Vqc \\in DOMAIN(a_VARIABLEunde_pcunde_a))<=>(zenon_Vqc \\in a_CONSTANTunde_Procunde_a))) ==> ?z_hd ==> (~(a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_pcunde_a))) ==> FALSE" (is "?z_hdv ==> _ ==> ?z_heb ==> FALSE")
 proof -
  assume z_Hdv:"?z_hdv" (is "\\A x : ?z_hed(x)")
  assume z_Hd:"?z_hd"
  assume z_Heb:"?z_heb" (is "~?z_hec")
  have z_Hee: "?z_hed(a_CONSTANTunde_punde_1unde_a)"
  by (rule zenon_all_0 [of "?z_hed" "a_CONSTANTunde_punde_1unde_a", OF z_Hdv])
  show FALSE
  proof (rule zenon_equiv [OF z_Hee])
   assume z_Heb:"?z_heb"
   assume z_Hef:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hef z_Hd])
  next
   assume z_Hec:"?z_hec"
   assume z_Hd:"?z_hd"
   show FALSE
   by (rule notE [OF z_Heb z_Hec])
  qed
 qed
 assume z_Ho:"((a_VARIABLEunde_pcunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~=(a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "?z_heg~=?z_heh")
 have z_Hp: "?z_hp" (is "?z_hq&_")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hq: "?z_hq" (is "?z_hr&?z_hcb")
 by (rule zenon_and_0 [OF z_Hp])
 have z_Hr: "?z_hr" (is "?z_hs&?z_hy")
 by (rule zenon_and_0 [OF z_Hq])
 have z_Hy: "?z_hy" (is "?z_hz&?z_hbc")
 by (rule zenon_and_1 [OF z_Hr])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbk")
 by (rule zenon_and_1 [OF z_Hy])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Hbc])
 have z_Hei: "(DOMAIN(a_VARIABLEunde_pcunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hdz=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_Procunde_a" "{''a'', ''b'', ''Done''}", OF z_Hbd])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hj])
  assume z_Hdf:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hdg~=_")
  assume z_Hdi:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hdj&?z_hdm")
  have z_Hdj: "?z_hdj" (is "_=?z_hdl")
  by (rule zenon_and_0 [OF z_Hdi])
  have z_Hdv: "(\\A zenon_Vqc:((zenon_Vqc \\in ?z_hdz)<=>(zenon_Vqc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hed(x)")
  by (rule zenon_setequal_0 [of "?z_hdz" "a_CONSTANTunde_Procunde_a", OF z_Hei])
  have z_Hel: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_hdl))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_hdl)))&(\\A zenon_Vccl:((a_VARIABLEunde_pcunde_hash_primea[zenon_Vccl])=(?z_hdl[zenon_Vccl]))))" (is "?z_hem&?z_het")
  by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_hdl", OF z_Hdj])
  have z_Het: "?z_het" (is "\\A x : ?z_hey(x)")
  by (rule zenon_and_1 [OF z_Hel])
  have z_Hez: "?z_hey(a_CONSTANTunde_punde_1unde_a)" (is "_=?z_hfa")
  by (rule zenon_all_0 [of "?z_hey" "a_CONSTANTunde_punde_1unde_a", OF z_Het])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Voal. (?z_heg=zenon_Voal))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "''b''" "a_CONSTANTunde_punde_1unde_a", OF z_Hez])
   assume z_Hec:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz)" (is "?z_hec")
   assume z_Hfe:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hff:"(?z_heg=''b'')" (is "_=?z_hbi")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfe z_Hf])
  next
   assume z_Hec:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz)" (is "?z_hec")
   assume z_Hfg:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfh:"(?z_heg=?z_heh)"
   show FALSE
   by (rule notE [OF z_Ho z_Hfh])
  next
   assume z_Heb:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz))" (is "~?z_hec")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdv z_Hd z_Heb])
  qed
 next
  assume z_Hfi:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hfj")
  assume z_Hdo:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hdp&?z_hdt")
  have z_Hdt: "?z_hdt" (is "_=?z_hdu")
  by (rule zenon_and_1 [OF z_Hdo])
  have z_Hdv: "(\\A zenon_Vqc:((zenon_Vqc \\in ?z_hdz)<=>(zenon_Vqc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hed(x)")
  by (rule zenon_setequal_0 [of "?z_hdz" "a_CONSTANTunde_Procunde_a", OF z_Hei])
  have z_Hfk: "(((isAFcn(a_VARIABLEunde_pcunde_hash_primea)<=>isAFcn(?z_hdu))&(DOMAIN(a_VARIABLEunde_pcunde_hash_primea)=DOMAIN(?z_hdu)))&(\\A zenon_Vjd:((a_VARIABLEunde_pcunde_hash_primea[zenon_Vjd])=(?z_hdu[zenon_Vjd]))))" (is "?z_hfl&?z_hfq")
  by (rule zenon_funequal_0 [of "a_VARIABLEunde_pcunde_hash_primea" "?z_hdu", OF z_Hdt])
  have z_Hfq: "?z_hfq" (is "\\A x : ?z_hfv(x)")
  by (rule zenon_and_1 [OF z_Hfk])
  have z_Hfw: "?z_hfv(a_CONSTANTunde_punde_1unde_a)" (is "_=?z_hfx")
  by (rule zenon_all_0 [of "?z_hfv" "a_CONSTANTunde_punde_1unde_a", OF z_Hfq])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Voal. (?z_heg=zenon_Voal))" "a_VARIABLEunde_pcunde_a" "a_CONSTANTunde_punde_a" "''Done''" "a_CONSTANTunde_punde_1unde_a", OF z_Hfw])
   assume z_Hec:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz)" (is "?z_hec")
   assume z_Hfe:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfy:"(?z_heg=''Done'')" (is "_=?z_hbj")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfe z_Hf])
  next
   assume z_Hec:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz)" (is "?z_hec")
   assume z_Hfg:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfh:"(?z_heg=?z_heh)"
   show FALSE
   by (rule notE [OF z_Ho z_Hfh])
  next
   assume z_Heb:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz))" (is "~?z_hec")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdv z_Hd z_Heb])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 218"; *} qed
lemma ob'219:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'49: "((((((((((a_VARIABLEunde_A1unde_a) \<in> ([(Nat) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_resultunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_pcunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ({(''a''), (''b''), (''Done'')})]))) & (((a_VARIABLEunde_knownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_notKnownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (Nat)))]))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))))))) \<and> ((\<forall> a_CONSTANTunde_iunde_a \<in> (Nat) : (((((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a))) \<noteq> ({}))) \<Rightarrow> ((geq (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))), (a_CONSTANTunde_iunde_a))))))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (\<forall> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((leq ((a_CONSTANTunde_iunde_a), ((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) & (((a_CONSTANTunde_punde_a) \<in> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Leftrightarrow> (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''Done''))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Rightarrow> (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'50: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_punde_1unde_a
assumes a_CONSTANTunde_punde_1unde_a_in : "(a_CONSTANTunde_punde_1unde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'75: "(((((a_CONSTANTunde_punde_1unde_a) = (a_CONSTANTunde_punde_a))) \<Longrightarrow> (((((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) \<noteq> ({}))) \<Leftrightarrow> (((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (''Done'')))))))"
assumes v'76: "(((a_CONSTANTunde_punde_1unde_a) \<noteq> (a_CONSTANTunde_punde_a)))"
assumes v'79: "((((a_CONSTANTunde_IsFiniteSetunde_a ((a_STATEunde_snapshotunde_a)))) \<and> (((a_STATEunde_snapshotunde_a) \<subseteq> (a_CONSTANTunde_Procunde_a)))))"
assumes v'80: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'81: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'82: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'83: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'84: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'85: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'86: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
assumes v'87: "(((fapply (((a_VARIABLEunde_pcunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_1unde_a)))))"
shows "(((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_1unde_a)))))"(is "PROP ?ob'219")
proof -
ML_command {* writeln "*** TLAPS ENTER 219"; *}
show "PROP ?ob'219"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_213c06.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_213c06.znn.out
;; obligation #219
$hyp "v'49" (/\ (/\ (/\ (/\ (TLA.in a_VARIABLEunde_A1unde_a
(TLA.FuncSet arith.N (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_resultunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_pcunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.set "a" "b" "Done")))
(TLA.in a_VARIABLEunde_knownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_notKnownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET arith.N)))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b") (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))))))
(/\ (TLA.bAll arith.N ((a_CONSTANTunde_iunde_a) (=> (-. (= (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)
TLA.emptyset)) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a))))))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
(TLA.bAll (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))
(TLA.in a_CONSTANTunde_punde_a
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(<=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset)) (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"Done"))
(=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))
(= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))))
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'50" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_punde_1unde_a_in" (TLA.in a_CONSTANTunde_punde_1unde_a a_CONSTANTunde_Procunde_a)
$hyp "v'75" (=> (= a_CONSTANTunde_punde_1unde_a
a_CONSTANTunde_punde_a) (<=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_1unde_a)
TLA.emptyset))
(= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_1unde_a)
"Done")))
$hyp "v'76" (-. (= a_CONSTANTunde_punde_1unde_a
a_CONSTANTunde_punde_a))
$hyp "v'79" (/\ (a_CONSTANTunde_IsFiniteSetunde_a a_STATEunde_snapshotunde_a)
(TLA.subseteq a_STATEunde_snapshotunde_a
a_CONSTANTunde_Procunde_a))
$hyp "v'80" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'81" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'82" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'83" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'84" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'85" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'86" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$hyp "v'87" (= (TLA.fapply a_VARIABLEunde_pcunde_hash_primea a_CONSTANTunde_punde_1unde_a)
(TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_1unde_a))
$goal (= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_1unde_a)
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_1unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((((a_VARIABLEunde_A1unde_a \\in FuncSet(Nat, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_resultunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''}))&((a_VARIABLEunde_knownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_notKnownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(Nat)))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})))))))))&(bAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])~={})=>(a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. ((((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))&((a_CONSTANTunde_punde_a \\in (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))&((((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})<=>((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''Done''))&(((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})=>((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))))))&a_STATEunde_InvCunde_a)&a_STATEunde_GFXCorrectunde_a)" (is "?z_hq&_")
 using v'49 by blast
 have z_Hf:"(a_CONSTANTunde_punde_1unde_a~=a_CONSTANTunde_punde_a)"
 using v'76 by blast
 have z_Hd:"(a_CONSTANTunde_punde_1unde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hd")
 using a_CONSTANTunde_punde_1unde_a_in by blast
 have z_Hj:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hj")
 using v'82 by blast
 assume z_Hp:"((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "?z_hdw~=?z_hdx")
 have z_Hq: "?z_hq" (is "?z_hr&_")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hr: "?z_hr" (is "?z_hs&?z_hcc")
 by (rule zenon_and_0 [OF z_Hq])
 have z_Hs: "?z_hs" (is "?z_ht&?z_hz")
 by (rule zenon_and_0 [OF z_Hr])
 have z_Hz: "?z_hz" (is "?z_hba&?z_hbd")
 by (rule zenon_and_1 [OF z_Hs])
 have z_Hba: "?z_hba"
 by (rule zenon_and_0 [OF z_Hz])
 have z_Hdy: "(DOMAIN(a_VARIABLEunde_resultunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hdz=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hba])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hj])
  assume z_Hdg:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hdh~=_")
  assume z_Hdj:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hdk&?z_hdn")
  have z_Hdn: "?z_hdn"
  by (rule zenon_and_1 [OF z_Hdj])
  show FALSE
  proof (rule zenon_noteq [of "?z_hdx"])
   have z_Hec: "(?z_hdx~=?z_hdx)"
   by (rule subst [where P="(\<lambda>zenon_Vden. ((zenon_Vden[a_CONSTANTunde_punde_1unde_a])~=?z_hdx))", OF z_Hdn], fact z_Hp)
   thus "(?z_hdx~=?z_hdx)" .
  qed
 next
  assume z_Heh:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hei")
  assume z_Hdp:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hdq&?z_hdu")
  have z_Hdq: "?z_hdq" (is "_=?z_hdr")
  by (rule zenon_and_0 [OF z_Hdp])
  have z_Hej: "(\\A zenon_Vmc:((zenon_Vmc \\in ?z_hdz)<=>(zenon_Vmc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_heo(x)")
  by (rule zenon_setequal_0 [of "?z_hdz" "a_CONSTANTunde_Procunde_a", OF z_Hdy])
  have z_Hep: "(((isAFcn(a_VARIABLEunde_resultunde_hash_primea)<=>isAFcn(?z_hdr))&(DOMAIN(a_VARIABLEunde_resultunde_hash_primea)=DOMAIN(?z_hdr)))&(\\A zenon_Vmd:((a_VARIABLEunde_resultunde_hash_primea[zenon_Vmd])=(?z_hdr[zenon_Vmd]))))" (is "?z_heq&?z_hex")
  by (rule zenon_funequal_0 [of "a_VARIABLEunde_resultunde_hash_primea" "?z_hdr", OF z_Hdq])
  have z_Hex: "?z_hex" (is "\\A x : ?z_hfc(x)")
  by (rule zenon_and_1 [OF z_Hep])
  have z_Hfd: "?z_hfc(a_CONSTANTunde_punde_1unde_a)" (is "_=?z_hfe")
  by (rule zenon_all_0 [of "?z_hfc" "a_CONSTANTunde_punde_1unde_a", OF z_Hex])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vxbn. (?z_hdw=zenon_Vxbn))" "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_punde_a" "(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])" "a_CONSTANTunde_punde_1unde_a", OF z_Hfd])
   assume z_Hfi:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz)" (is "?z_hfi")
   assume z_Hfj:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfk:"(?z_hdw=(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))" (is "_=?z_hds")
   show FALSE
   by (rule zenon_eqsym [OF z_Hfj z_Hf])
  next
   assume z_Hfi:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz)" (is "?z_hfi")
   assume z_Hfl:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hfm:"(?z_hdw=?z_hdx)"
   show FALSE
   by (rule notE [OF z_Hp z_Hfm])
  next
   assume z_Hfn:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hdz))" (is "~?z_hfi")
   have z_Hfo: "?z_heo(a_CONSTANTunde_punde_1unde_a)"
   by (rule zenon_all_0 [of "?z_heo" "a_CONSTANTunde_punde_1unde_a", OF z_Hej])
   show FALSE
   proof (rule zenon_equiv [OF z_Hfo])
    assume z_Hfn:"(~?z_hfi)"
    assume z_Hfp:"(~?z_hd)"
    show FALSE
    by (rule notE [OF z_Hfp z_Hd])
   next
    assume z_Hfi:"?z_hfi"
    assume z_Hd:"?z_hd"
    show FALSE
    by (rule notE [OF z_Hfn z_Hfi])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 219"; *} qed
lemma ob'220:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'49: "((((((((((a_VARIABLEunde_A1unde_a) \<in> ([(Nat) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_resultunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_pcunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ({(''a''), (''b''), (''Done'')})]))) & (((a_VARIABLEunde_knownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_notKnownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (Nat)))]))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))))))) \<and> ((\<forall> a_CONSTANTunde_iunde_a \<in> (Nat) : (((((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a))) \<noteq> ({}))) \<Rightarrow> ((geq (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))), (a_CONSTANTunde_iunde_a))))))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (\<forall> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((leq ((a_CONSTANTunde_iunde_a), ((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) & (((a_CONSTANTunde_punde_a) \<in> (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Leftrightarrow> (((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''Done''))))) & (((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) \<Rightarrow> (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))))))))))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'50: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_punde_1unde_a
assumes a_CONSTANTunde_punde_1unde_a_in : "(a_CONSTANTunde_punde_1unde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'76: "((((a_CONSTANTunde_IsFiniteSetunde_a ((a_STATEunde_snapshotunde_a)))) \<and> (((a_STATEunde_snapshotunde_a) \<subseteq> (a_CONSTANTunde_Procunde_a)))))"
assumes v'77: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'78: "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1)))))) \<in> (Nat))))"
assumes v'79: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'80: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'81: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'82: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'83: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
shows "(((((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) \<noteq> ({}))) \<Rightarrow> (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a))) = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_1unde_a)))))))"(is "PROP ?ob'220")
proof -
ML_command {* writeln "*** TLAPS ENTER 220"; *}
show "PROP ?ob'220"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_41c302.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_41c302.znn.out
;; obligation #220
$hyp "v'49" (/\ (/\ (/\ (/\ (TLA.in a_VARIABLEunde_A1unde_a
(TLA.FuncSet arith.N (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_resultunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_pcunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.set "a" "b" "Done")))
(TLA.in a_VARIABLEunde_knownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_notKnownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET arith.N)))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b") (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))))))
(/\ (TLA.bAll arith.N ((a_CONSTANTunde_iunde_a) (=> (-. (= (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)
TLA.emptyset)) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a))))))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (/\ (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
(TLA.bAll (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (arith.le a_CONSTANTunde_iunde_a
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))
(TLA.in a_CONSTANTunde_punde_a
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))
(<=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset)) (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"Done"))
(=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
TLA.emptyset))
(= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a))))))))
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'50" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_punde_1unde_a_in" (TLA.in a_CONSTANTunde_punde_1unde_a a_CONSTANTunde_Procunde_a)
$hyp "v'76" (/\ (a_CONSTANTunde_IsFiniteSetunde_a a_STATEunde_snapshotunde_a)
(TLA.subseteq a_STATEunde_snapshotunde_a
a_CONSTANTunde_Procunde_a))
$hyp "v'77" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'78" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (TLA.in (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a_1))
arith.N)))
$hyp "v'79" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'80" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'81" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'82" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'83" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$goal (=> (-. (= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_1unde_a)
TLA.emptyset))
(= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_1unde_a)
(TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_1unde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((((a_VARIABLEunde_A1unde_a \\in FuncSet(Nat, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_resultunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''}))&((a_VARIABLEunde_knownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_notKnownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(Nat)))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})))))))))&(bAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])~={})=>(a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. ((((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))&((a_CONSTANTunde_punde_a \\in (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))&((((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})<=>((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''Done''))&(((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])~={})=>((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))))))))))&a_STATEunde_InvCunde_a)&a_STATEunde_GFXCorrectunde_a)" (is "?z_hn&_")
 using v'49 by blast
 have z_Hk:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hdd")
 using v'82 by blast
 have z_Hj:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hdm")
 using v'81 by blast
 have z_Hh:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hh")
 using v'79 by blast
 have z_Hc:"(a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hc")
 using a_CONSTANTunde_punde_a_in by blast
 have z_Hi:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''a'')" (is "?z_hbu=?z_hbf")
 using v'80 by blast
 have z_Hd:"(a_CONSTANTunde_punde_1unde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hd")
 using a_CONSTANTunde_punde_1unde_a_in by blast
 have zenon_L1_: "((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_1unde_a])) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hef ==> ?z_hdx ==> FALSE")
 proof -
  assume z_Hef:"?z_hef" (is "?z_heg~=?z_heh")
  assume z_Hdx:"?z_hdx"
  show FALSE
  proof (rule zenon_noteq [of "?z_heh"])
   have z_Hei: "(?z_heh~=?z_heh)"
   by (rule subst [where P="(\<lambda>zenon_Vffca. ((zenon_Vffca[a_CONSTANTunde_punde_1unde_a])~=?z_heh))", OF z_Hdx], fact z_Hef)
   thus "(?z_heh~=?z_heh)" .
  qed
 qed
 have zenon_L2_: "(~((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_1unde_a])~={})) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> ((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~={}) ==> FALSE" (is "?z_hen ==> ?z_hdx ==> ?z_hep ==> FALSE")
 proof -
  assume z_Hen:"?z_hen" (is "~~?z_heq")
  assume z_Hdx:"?z_hdx"
  assume z_Hep:"?z_hep" (is "?z_heg~=_")
  have z_Heq: "?z_heq" (is "?z_heh=_")
  by (rule zenon_notnot_0 [OF z_Hen])
  show FALSE
  proof (rule notE [OF z_Hep])
   have z_Her: "(?z_heh=?z_heg)"
   proof (rule zenon_nnpp [of "(?z_heh=?z_heg)"])
    assume z_Hes:"(?z_heh~=?z_heg)"
    show FALSE
    proof (rule zenon_em [of "(?z_heg=?z_heg)"])
     assume z_Het:"(?z_heg=?z_heg)"
     show FALSE
     proof (rule notE [OF z_Hes])
      have z_Heu: "(?z_heg=?z_heh)"
      proof (rule zenon_nnpp [of "(?z_heg=?z_heh)"])
       assume z_Hef:"(?z_heg~=?z_heh)"
       show FALSE
       by (rule zenon_L1_ [OF z_Hef z_Hdx])
      qed
      have z_Her: "(?z_heh=?z_heg)"
      by (rule subst [where P="(\<lambda>zenon_Vgfca. (zenon_Vgfca=?z_heg))", OF z_Heu], fact z_Het)
      thus "(?z_heh=?z_heg)" .
     qed
    next
     assume z_Hey:"(?z_heg~=?z_heg)"
     show FALSE
     by (rule zenon_noteq [OF z_Hey])
    qed
   qed
   have z_Hez: "(?z_heg={})"
   by (rule subst [where P="(\<lambda>zenon_Vld. (zenon_Vld={}))", OF z_Her], fact z_Heq)
   thus "(?z_heg={})" .
  qed
 qed
 have zenon_L3_: "((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=?z_hbu) ==> (a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a) ==> FALSE" (is "?z_hfd ==> ?z_hff ==> FALSE")
 proof -
  assume z_Hfd:"?z_hfd" (is "?z_hfe~=_")
  assume z_Hff:"?z_hff"
  show FALSE
  proof (rule zenon_noteq [of "?z_hbu"])
   have z_Hfg: "(a_CONSTANTunde_punde_1unde_a=a_CONSTANTunde_punde_a)"
   by (rule sym [OF z_Hff])
   have z_Hfh: "(?z_hbu~=?z_hbu)"
   by (rule subst [where P="(\<lambda>zenon_Vifca. ((a_VARIABLEunde_pcunde_a[zenon_Vifca])~=?z_hbu))", OF z_Hfg], fact z_Hfd)
   thus "(?z_hbu~=?z_hbu)" .
  qed
 qed
 have zenon_L4_: "(?z_hbu=?z_hbf) ==> ((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])=''Done'') ==> (a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a) ==> FALSE" (is "?z_hi ==> ?z_hfm ==> ?z_hff ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hfm:"?z_hfm" (is "?z_hfe=?z_hbh")
  assume z_Hff:"?z_hff"
  have z_Hfn: "(?z_hbh~=?z_hbf)"
  by auto
  have z_Hfd: "(?z_hfe~=?z_hbu)"
  by (rule zenon_stringdiffll [OF z_Hfn z_Hfm z_Hi])
   show FALSE
   by (rule zenon_L3_ [OF z_Hfd z_Hff])
 qed
 have zenon_L5_: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (~(a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a))) ==> ?z_hd ==> FALSE" (is "?z_hfo ==> ?z_hfq ==> _ ==> FALSE")
 proof -
  assume z_Hfo:"?z_hfo" (is "?z_hfp=_")
  assume z_Hfq:"?z_hfq" (is "~?z_hfr")
  assume z_Hd:"?z_hd"
  have z_Hfs: "(\\A zenon_Vxc:((zenon_Vxc \\in ?z_hfp)<=>(zenon_Vxc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hfx(x)")
  by (rule zenon_setequal_0 [of "?z_hfp" "a_CONSTANTunde_Procunde_a", OF z_Hfo])
  have z_Hfy: "?z_hfx(a_CONSTANTunde_punde_1unde_a)"
  by (rule zenon_all_0 [of "?z_hfx" "a_CONSTANTunde_punde_1unde_a", OF z_Hfs])
  show FALSE
  proof (rule zenon_equiv [OF z_Hfy])
   assume z_Hfq:"?z_hfq"
   assume z_Hfz:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hfz z_Hd])
  next
   assume z_Hfr:"?z_hfr"
   assume z_Hd:"?z_hd"
   show FALSE
   by (rule notE [OF z_Hfq z_Hfr])
  qed
 qed
 have zenon_L6_: "(\\A zenon_Vnc:((zenon_Vnc \\in DOMAIN(a_VARIABLEunde_resultunde_a))<=>(zenon_Vnc \\in a_CONSTANTunde_Procunde_a))) ==> ?z_hd ==> (~(a_CONSTANTunde_punde_1unde_a \\in DOMAIN(a_VARIABLEunde_resultunde_a))) ==> FALSE" (is "?z_hga ==> _ ==> ?z_hgg ==> FALSE")
 proof -
  assume z_Hga:"?z_hga" (is "\\A x : ?z_hgi(x)")
  assume z_Hd:"?z_hd"
  assume z_Hgg:"?z_hgg" (is "~?z_hgh")
  have z_Hgj: "?z_hgi(a_CONSTANTunde_punde_1unde_a)"
  by (rule zenon_all_0 [of "?z_hgi" "a_CONSTANTunde_punde_1unde_a", OF z_Hga])
  show FALSE
  proof (rule zenon_equiv [OF z_Hgj])
   assume z_Hgg:"?z_hgg"
   assume z_Hfz:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hfz z_Hd])
  next
   assume z_Hgh:"?z_hgh"
   assume z_Hd:"?z_hd"
   show FALSE
   by (rule notE [OF z_Hgg z_Hgh])
  qed
 qed
 have zenon_L7_: "(DOMAIN(a_VARIABLEunde_resultunde_a)=a_CONSTANTunde_Procunde_a) ==> ((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_1unde_a])) ==> (a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a) ==> ?z_hd ==> (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (?z_hdm[a_CONSTANTunde_punde_a]))) ==> FALSE" (is "?z_hgk ==> ?z_hef ==> ?z_hgl ==> _ ==> ?z_hgm ==> FALSE")
 proof -
  assume z_Hgk:"?z_hgk" (is "?z_hge=_")
  assume z_Hef:"?z_hef" (is "?z_heg~=?z_heh")
  assume z_Hgl:"?z_hgl"
  assume z_Hd:"?z_hd"
  assume z_Hgm:"?z_hgm" (is "_=?z_hgn")
  have z_Hga: "(\\A zenon_Vnc:((zenon_Vnc \\in ?z_hge)<=>(zenon_Vnc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hgi(x)")
  by (rule zenon_setequal_0 [of "?z_hge" "a_CONSTANTunde_Procunde_a", OF z_Hgk])
  have z_Hgp: "(((isAFcn(a_VARIABLEunde_resultunde_hash_primea)<=>isAFcn(?z_hgn))&(DOMAIN(a_VARIABLEunde_resultunde_hash_primea)=DOMAIN(?z_hgn)))&(\\A zenon_Vsd:((a_VARIABLEunde_resultunde_hash_primea[zenon_Vsd])=(?z_hgn[zenon_Vsd]))))" (is "?z_hgq&?z_hgx")
  by (rule zenon_funequal_0 [of "a_VARIABLEunde_resultunde_hash_primea" "?z_hgn", OF z_Hgm])
  have z_Hgx: "?z_hgx" (is "\\A x : ?z_hhc(x)")
  by (rule zenon_and_1 [OF z_Hgp])
  have z_Hgj: "?z_hgi(a_CONSTANTunde_punde_1unde_a)" (is "?z_hgh<=>_")
  by (rule zenon_all_0 [of "?z_hgi" "a_CONSTANTunde_punde_1unde_a", OF z_Hga])
  show FALSE
  proof (rule zenon_equiv [OF z_Hgj])
   assume z_Hgg:"(~?z_hgh)"
   assume z_Hfz:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hfz z_Hd])
  next
   assume z_Hgh:"?z_hgh"
   assume z_Hd:"?z_hd"
   have z_Hhd: "?z_hhc(a_CONSTANTunde_punde_1unde_a)" (is "_=?z_hhe")
   by (rule zenon_all_0 [of "?z_hhc" "a_CONSTANTunde_punde_1unde_a", OF z_Hgx])
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vlsk. (?z_heg=zenon_Vlsk))" "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_punde_a" "(?z_hdm[a_CONSTANTunde_punde_a])" "a_CONSTANTunde_punde_1unde_a", OF z_Hhd])
    assume z_Hgh:"?z_hgh"
    assume z_Hff:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
    assume z_Hhi:"(?z_heg=(?z_hdm[a_CONSTANTunde_punde_a]))" (is "_=?z_hgo")
    show FALSE
    by (rule notE [OF z_Hgl z_Hff])
   next
    assume z_Hgh:"?z_hgh"
    assume z_Hgl:"?z_hgl"
    assume z_Heu:"(?z_heg=?z_heh)"
    show FALSE
    by (rule notE [OF z_Hef z_Heu])
   next
    assume z_Hgg:"(~?z_hgh)"
    show FALSE
    by (rule notE [OF z_Hgg z_Hgh])
   qed
  qed
 qed
 have zenon_L8_: "(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) ==> ?z_hd ==> ((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~={}) ==> (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (?z_hdm[a_CONSTANTunde_punde_a]))) ==> (a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a) ==> (DOMAIN(a_VARIABLEunde_resultunde_a)=a_CONSTANTunde_Procunde_a) ==> ((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a])) ==> FALSE" (is "?z_hhj ==> _ ==> ?z_hep ==> ?z_hgm ==> ?z_hgl ==> ?z_hgk ==> ?z_hig ==> FALSE")
 proof -
  assume z_Hhj:"?z_hhj" (is "\\A x : ?z_hii(x)")
  assume z_Hd:"?z_hd"
  assume z_Hep:"?z_hep" (is "?z_heg~=_")
  assume z_Hgm:"?z_hgm" (is "_=?z_hgn")
  assume z_Hgl:"?z_hgl"
  assume z_Hgk:"?z_hgk" (is "?z_hge=_")
  assume z_Hig:"?z_hig" (is "_~=?z_hih")
  have z_Hij: "?z_hii(a_CONSTANTunde_punde_1unde_a)" (is "_=>?z_hik")
  by (rule zenon_all_0 [of "?z_hii" "a_CONSTANTunde_punde_1unde_a", OF z_Hhj])
  show FALSE
  proof (rule zenon_imply [OF z_Hij])
   assume z_Hfz:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hfz z_Hd])
  next
   assume z_Hik:"?z_hik" (is "?z_hil&?z_him")
   have z_Him: "?z_him" (is "?z_hin&?z_hio")
   by (rule zenon_and_1 [OF z_Hik])
   have z_Hio: "?z_hio" (is "?z_hip&?z_hiq")
   by (rule zenon_and_1 [OF z_Him])
   have z_Hip: "?z_hip" (is "?z_heo<=>?z_hfm")
   by (rule zenon_and_0 [OF z_Hio])
   have z_Hiq: "?z_hiq" (is "_=>?z_hir")
   by (rule zenon_and_1 [OF z_Hio])
   show FALSE
   proof (rule zenon_equiv [OF z_Hip])
    assume z_Hen:"(~?z_heo)" (is "~~?z_heq")
    assume z_His:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=''Done'')" (is "?z_hfe~=?z_hbh")
    have z_Heq: "?z_heq" (is "?z_heh=_")
    by (rule zenon_notnot_0 [OF z_Hen])
    have z_Hit: "(\\A zenon_Vusk:(~(zenon_Vusk \\in ?z_heh)))" (is "\\A x : ?z_hix(x)")
    by (rule zenon_setequalempty_0 [of "?z_heh", OF z_Heq])
    have z_Hiy: "(~(\\A zenon_Vwa:((zenon_Vwa \\in ?z_heg)<=>(zenon_Vwa \\in {}))))" (is "~(\\A x : ?z_hje(x))")
    by (rule zenon_notsetequal_0 [of "?z_heg" "{}", OF z_Hep])
    have z_Hjf: "(\\E zenon_Vwa:(~((zenon_Vwa \\in ?z_heg)<=>(zenon_Vwa \\in {}))))" (is "\\E x : ?z_hjh(x)")
    by (rule zenon_notallex_0 [of "?z_hje", OF z_Hiy])
    have z_Hji: "?z_hjh((CHOOSE zenon_Vwa:(~((zenon_Vwa \\in ?z_heg)<=>(zenon_Vwa \\in {})))))" (is "~(?z_hjk<=>?z_hjl)")
    by (rule zenon_ex_choose_0 [of "?z_hjh", OF z_Hjf])
    show FALSE
    proof (rule zenon_notequiv [OF z_Hji])
     assume z_Hjm:"(~?z_hjk)"
     assume z_Hjl:"?z_hjl"
     show FALSE
     by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vwa:(~((zenon_Vwa \\in ?z_heg)<=>(zenon_Vwa \\in {}))))", OF z_Hjl])
    next
     assume z_Hjk:"?z_hjk"
     assume z_Hjn:"(~?z_hjl)"
     have z_Hjo: "?z_hix((CHOOSE zenon_Vwa:(~((zenon_Vwa \\in ?z_heg)<=>(zenon_Vwa \\in {})))))" (is "~?z_hjp")
     by (rule zenon_all_0 [of "?z_hix" "(CHOOSE zenon_Vwa:(~((zenon_Vwa \\in ?z_heg)<=>(zenon_Vwa \\in {}))))", OF z_Hit])
     show FALSE
     proof (rule notE [OF z_Hjo])
      have z_Heu: "(?z_heg=?z_heh)"
      proof (rule zenon_nnpp [of "(?z_heg=?z_heh)"])
       assume z_Hef:"(?z_heg~=?z_heh)"
       show FALSE
       by (rule zenon_L7_ [OF z_Hgk z_Hef z_Hgl z_Hd z_Hgm])
      qed
      have z_Hjp: "?z_hjp"
      by (rule subst [where P="(\<lambda>zenon_Vjfca. ((CHOOSE zenon_Vwa:(~((zenon_Vwa \\in ?z_heg)<=>(zenon_Vwa \\in {})))) \\in zenon_Vjfca))", OF z_Heu], fact z_Hjk)
      thus "?z_hjp" .
     qed
    qed
   next
    assume z_Heo:"?z_heo" (is "?z_heh~=_")
    assume z_Hfm:"?z_hfm" (is "?z_hfe=?z_hbh")
    show FALSE
    proof (rule zenon_imply [OF z_Hiq])
     assume z_Hen:"(~?z_heo)" (is "~~?z_heq")
     show FALSE
     by (rule notE [OF z_Hen z_Heo])
    next
     assume z_Hir:"?z_hir"
     show FALSE
     proof (rule notE [OF z_Hig])
      have z_Her: "(?z_heh=?z_heg)"
      proof (rule zenon_nnpp [of "(?z_heh=?z_heg)"])
       assume z_Hes:"(?z_heh~=?z_heg)"
       show FALSE
       proof (rule zenon_em [of "(?z_heg=?z_heg)"])
        assume z_Het:"(?z_heg=?z_heg)"
        show FALSE
        proof (rule notE [OF z_Hes])
         have z_Heu: "(?z_heg=?z_heh)"
         proof (rule zenon_nnpp [of "(?z_heg=?z_heh)"])
          assume z_Hef:"(?z_heg~=?z_heh)"
          show FALSE
          by (rule zenon_L7_ [OF z_Hgk z_Hef z_Hgl z_Hd z_Hgm])
         qed
         have z_Her: "(?z_heh=?z_heg)"
         by (rule subst [where P="(\<lambda>zenon_Vgfca. (zenon_Vgfca=?z_heg))", OF z_Heu], fact z_Het)
         thus "(?z_heh=?z_heg)" .
        qed
       next
        assume z_Hey:"(?z_heg~=?z_heg)"
        show FALSE
        by (rule zenon_noteq [OF z_Hey])
       qed
      qed
      have z_Hjt: "(?z_heg=?z_hih)"
      by (rule subst [where P="(\<lambda>zenon_Vlfca. (zenon_Vlfca=?z_hih))", OF z_Her], fact z_Hir)
      thus "(?z_heg=?z_hih)" .
     qed
    qed
   qed
  qed
 qed
 have zenon_L9_: "((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~=(?z_hdm[a_CONSTANTunde_punde_1unde_a])) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> ((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~={}) ==> (\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) ==> (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (?z_hdm[a_CONSTANTunde_punde_a]))) ==> (a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> ?z_hd ==> (DOMAIN(a_VARIABLEunde_resultunde_a)=a_CONSTANTunde_Procunde_a) ==> FALSE" (is "?z_hjx ==> ?z_hfo ==> ?z_hep ==> ?z_hhj ==> ?z_hgm ==> ?z_hjz ==> _ ==> ?z_hgk ==> FALSE")
 proof -
  assume z_Hjx:"?z_hjx" (is "?z_heg~=?z_hjy")
  assume z_Hfo:"?z_hfo" (is "?z_hfp=_")
  assume z_Hep:"?z_hep"
  assume z_Hhj:"?z_hhj" (is "\\A x : ?z_hii(x)")
  assume z_Hgm:"?z_hgm" (is "_=?z_hgn")
  assume z_Hjz:"?z_hjz"
  assume z_Hd:"?z_hd"
  assume z_Hgk:"?z_hgk" (is "?z_hge=_")
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vua. (?z_heg~=zenon_Vua))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hjx])
   assume z_Hfr:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hfp)" (is "?z_hfr")
   assume z_Hff:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hkd:"(?z_heg~=((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_~=?z_hdn")
   have z_Hga: "(\\A zenon_Vnc:((zenon_Vnc \\in ?z_hge)<=>(zenon_Vnc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hgi(x)")
   by (rule zenon_setequal_0 [of "?z_hge" "a_CONSTANTunde_Procunde_a", OF z_Hgk])
   have z_Hgp: "(((isAFcn(a_VARIABLEunde_resultunde_hash_primea)<=>isAFcn(?z_hgn))&(DOMAIN(a_VARIABLEunde_resultunde_hash_primea)=DOMAIN(?z_hgn)))&(\\A zenon_Vsd:((a_VARIABLEunde_resultunde_hash_primea[zenon_Vsd])=(?z_hgn[zenon_Vsd]))))" (is "?z_hgq&?z_hgx")
   by (rule zenon_funequal_0 [of "a_VARIABLEunde_resultunde_hash_primea" "?z_hgn", OF z_Hgm])
   have z_Hgx: "?z_hgx" (is "\\A x : ?z_hhc(x)")
   by (rule zenon_and_1 [OF z_Hgp])
   have z_Hhd: "?z_hhc(a_CONSTANTunde_punde_1unde_a)" (is "_=?z_hhe")
   by (rule zenon_all_0 [of "?z_hhc" "a_CONSTANTunde_punde_1unde_a", OF z_Hgx])
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vlsk. (?z_heg=zenon_Vlsk))" "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_punde_a" "(?z_hdm[a_CONSTANTunde_punde_a])" "a_CONSTANTunde_punde_1unde_a", OF z_Hhd])
    assume z_Hgh:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hge)" (is "?z_hgh")
    assume z_Hff:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
    assume z_Hhi:"(?z_heg=(?z_hdm[a_CONSTANTunde_punde_a]))" (is "_=?z_hgo")
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vlsk. (?z_heg=zenon_Vlsk))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "?z_hdn" "a_CONSTANTunde_punde_a", OF z_Hhi])
     assume z_Hjz:"?z_hjz"
     assume z_Hke:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_a)"
     assume z_Hkf:"(?z_heg=?z_hdn)"
     show FALSE
     by (rule notE [OF z_Hkd z_Hkf])
    next
     assume z_Hjz:"?z_hjz"
     assume z_Hkg:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_a)"
     assume z_Hkh:"(?z_heg=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))" (is "_=?z_hcq")
     show FALSE
     by (rule zenon_noteq [OF z_Hkg])
    next
     assume z_Hki:"(~?z_hjz)"
     show FALSE
     by (rule notE [OF z_Hki z_Hjz])
    qed
   next
    assume z_Hgh:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hge)" (is "?z_hgh")
    assume z_Hgl:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
    assume z_Heu:"(?z_heg=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "_=?z_heh")
    show FALSE
    by (rule notE [OF z_Hgl z_Hff])
   next
    assume z_Hgg:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hge))" (is "~?z_hgh")
    show FALSE
    by (rule zenon_L6_ [OF z_Hga z_Hd z_Hgg])
   qed
  next
   assume z_Hfr:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hfp)" (is "?z_hfr")
   assume z_Hgl:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hig:"(?z_heg~=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "_~=?z_hih")
   show FALSE
   by (rule zenon_L8_ [OF z_Hhj z_Hd z_Hep z_Hgm z_Hgl z_Hgk z_Hig])
  next
   assume z_Hfq:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hfp))" (is "~?z_hfr")
   show FALSE
   by (rule zenon_L5_ [OF z_Hfo z_Hfq z_Hd])
  qed
 qed
 have zenon_L10_: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (~(a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a))) ==> ?z_hc ==> FALSE" (is "?z_hfo ==> ?z_hki ==> _ ==> FALSE")
 proof -
  assume z_Hfo:"?z_hfo" (is "?z_hfp=_")
  assume z_Hki:"?z_hki" (is "~?z_hjz")
  assume z_Hc:"?z_hc"
  have z_Hfs: "(\\A zenon_Vxc:((zenon_Vxc \\in ?z_hfp)<=>(zenon_Vxc \\in a_CONSTANTunde_Procunde_a)))" (is "\\A x : ?z_hfx(x)")
  by (rule zenon_setequal_0 [of "?z_hfp" "a_CONSTANTunde_Procunde_a", OF z_Hfo])
  have z_Hkj: "?z_hfx(a_CONSTANTunde_punde_a)"
  by (rule zenon_all_0 [of "?z_hfx" "a_CONSTANTunde_punde_a", OF z_Hfs])
  show FALSE
  proof (rule zenon_equiv [OF z_Hkj])
   assume z_Hki:"?z_hki"
   assume z_Hkk:"(~?z_hc)"
   show FALSE
   by (rule notE [OF z_Hkk z_Hc])
  next
   assume z_Hjz:"?z_hjz"
   assume z_Hc:"?z_hc"
   show FALSE
   by (rule notE [OF z_Hki z_Hjz])
  qed
 qed
 have zenon_L11_: "(~(a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_notKnownunde_a))) ==> (a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_knownunde_a)) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> FALSE" (is "?z_hkl ==> ?z_hjz ==> ?z_hko ==> ?z_hfo ==> FALSE")
 proof -
  assume z_Hkl:"?z_hkl" (is "~?z_hkm")
  assume z_Hjz:"?z_hjz"
  assume z_Hko:"?z_hko" (is "?z_hkn=_")
  assume z_Hfo:"?z_hfo" (is "?z_hfp=_")
  show FALSE
  proof (rule notE [OF z_Hkl])
   have z_Hkp: "(?z_hfp=?z_hkn)"
   proof (rule zenon_nnpp [of "(?z_hfp=?z_hkn)"])
    assume z_Hkq:"(?z_hfp~=?z_hkn)"
    show FALSE
    proof (rule notE [OF z_Hkq])
     have z_Hkr: "(a_CONSTANTunde_Procunde_a=?z_hkn)"
     by (rule sym [OF z_Hko])
     have z_Hkp: "(?z_hfp=?z_hkn)"
     by (rule subst [where P="(\<lambda>zenon_Vmfca. (?z_hfp=zenon_Vmfca))", OF z_Hkr], fact z_Hfo)
     thus "(?z_hfp=?z_hkn)" .
    qed
   qed
   have z_Hkm: "?z_hkm"
   by (rule subst [where P="(\<lambda>zenon_Vnfca. (a_CONSTANTunde_punde_a \\in zenon_Vnfca))", OF z_Hkp], fact z_Hjz)
   thus "?z_hkm" .
  qed
 qed
 have zenon_L12_: "(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (?z_hdm[a_CONSTANTunde_punde_a]))) ==> ?z_hc ==> (DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a) ==> (DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a) ==> (~(a_CONSTANTunde_punde_a \\in DOMAIN(a_VARIABLEunde_notKnownunde_a))) ==> FALSE" (is "?z_hgm ==> _ ==> ?z_hfo ==> ?z_hko ==> ?z_hkl ==> FALSE")
 proof -
  assume z_Hgm:"?z_hgm" (is "_=?z_hgn")
  assume z_Hc:"?z_hc"
  assume z_Hfo:"?z_hfo" (is "?z_hfp=_")
  assume z_Hko:"?z_hko" (is "?z_hkn=_")
  assume z_Hkl:"?z_hkl" (is "~?z_hkm")
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vpd. (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, zenon_Vpd)))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_a", OF z_Hgm])
   assume z_Hjz:"(a_CONSTANTunde_punde_a \\in ?z_hfp)" (is "?z_hjz")
   assume z_Hke:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_a)"
   assume z_Hlc:"(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hld")
   show FALSE
   by (rule zenon_L11_ [OF z_Hkl z_Hjz z_Hko z_Hfo])
  next
   assume z_Hjz:"(a_CONSTANTunde_punde_a \\in ?z_hfp)" (is "?z_hjz")
   assume z_Hkg:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_a)"
   assume z_Hle:"(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a])))" (is "_=?z_hlf")
   show FALSE
   by (rule zenon_noteq [OF z_Hkg])
  next
   assume z_Hki:"(~(a_CONSTANTunde_punde_a \\in ?z_hfp))" (is "~?z_hjz")
   show FALSE
   by (rule zenon_L10_ [OF z_Hfo z_Hki z_Hc])
  qed
 qed
 assume z_Hm:"(~(((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])~={})=>((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_punde_1unde_a])=(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))))" (is "~(?z_hep=>?z_hlh)")
 have z_Hn: "?z_hn" (is "?z_ho&_")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Ho: "?z_ho" (is "?z_hp&?z_hbz")
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hp: "?z_hp" (is "?z_hq&?z_hw")
 by (rule zenon_and_0 [OF z_Ho])
 have z_Hbz: "?z_hbz" (is "?z_hca&?z_hci")
 by (rule zenon_and_1 [OF z_Ho])
 have z_Hci: "?z_hci"
 by (rule zenon_and_1 [OF z_Hbz])
 have z_Hw: "?z_hw" (is "?z_hx&?z_hba")
 by (rule zenon_and_1 [OF z_Hp])
 have z_Hx: "?z_hx"
 by (rule zenon_and_0 [OF z_Hw])
 have z_Hba: "?z_hba" (is "?z_hbb&?z_hbi")
 by (rule zenon_and_1 [OF z_Hw])
 have z_Hbi: "?z_hbi" (is "?z_hbj&?z_hbl")
 by (rule zenon_and_1 [OF z_Hba])
 have z_Hbj: "?z_hbj"
 by (rule zenon_and_0 [OF z_Hbi])
 have z_Hbl: "?z_hbl" (is "?z_hbm&?z_hbq")
 by (rule zenon_and_1 [OF z_Hbi])
 have z_Hbm: "?z_hbm"
 by (rule zenon_and_0 [OF z_Hbl])
 have z_Hhj_z_Hci: "(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>((((a_VARIABLEunde_pcunde_a[x])=''b'')=>bAll((a_VARIABLEunde_notKnownunde_a[x]), (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_iunde_a <= a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[x]))))))&((x \\in (a_VARIABLEunde_knownunde_a[x]))&((((a_VARIABLEunde_resultunde_a[x])~={})<=>((a_VARIABLEunde_pcunde_a[x])=''Done''))&(((a_VARIABLEunde_resultunde_a[x])~={})=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_knownunde_a[x])))))))) == ?z_hci" (is "?z_hhj == _")
 by (unfold bAll_def)
 have z_Hhj: "?z_hhj" (is "\\A x : ?z_hii(x)")
 by (unfold z_Hhj_z_Hci, fact z_Hci)
 have z_Hep: "?z_hep" (is "?z_heg~=_")
 by (rule zenon_notimply_0 [OF z_Hm])
 have z_Hlj: "(?z_heg~=(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_1unde_a]))" (is "_~=?z_hli")
 by (rule zenon_notimply_1 [OF z_Hm])
 have z_Hjx: "(?z_heg~=(?z_hdm[a_CONSTANTunde_punde_1unde_a]))" (is "_~=?z_hjy")
 by (rule subst [where P="(\<lambda>zenon_Vicca. (?z_heg~=(zenon_Vicca[a_CONSTANTunde_punde_1unde_a])))", OF z_Hj z_Hlj])
 have z_Hgk: "(DOMAIN(a_VARIABLEunde_resultunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hge=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_resultunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hx])
 have z_Hfo: "(DOMAIN(a_VARIABLEunde_knownunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hfp=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(a_CONSTANTunde_Procunde_a)", OF z_Hbj])
 have z_Hko: "(DOMAIN(a_VARIABLEunde_notKnownunde_a)=a_CONSTANTunde_Procunde_a)" (is "?z_hkn=_")
 by (rule zenon_in_funcset_1 [of "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_Procunde_a" "SUBSET(Nat)", OF z_Hbm])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hh])
  assume z_Hdr:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hds~=_")
  assume z_Hdt:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hdu&?z_hdx")
  have z_Hdx: "?z_hdx"
  by (rule zenon_and_1 [OF z_Hdt])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vua. (?z_heg~=zenon_Vua))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_1unde_a", OF z_Hjx])
   assume z_Hfr:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hfp)" (is "?z_hfr")
   assume z_Hff:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hkd:"(?z_heg~=((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_~=?z_hdn")
   have z_Hij: "?z_hii(a_CONSTANTunde_punde_1unde_a)" (is "_=>?z_hik")
   by (rule zenon_all_0 [of "?z_hii" "a_CONSTANTunde_punde_1unde_a", OF z_Hhj])
   show FALSE
   proof (rule zenon_imply [OF z_Hij])
    assume z_Hfz:"(~?z_hd)"
    show FALSE
    by (rule notE [OF z_Hfz z_Hd])
   next
    assume z_Hik:"?z_hik" (is "?z_hil&?z_him")
    have z_Him: "?z_him" (is "?z_hin&?z_hio")
    by (rule zenon_and_1 [OF z_Hik])
    have z_Hio: "?z_hio" (is "?z_hip&?z_hiq")
    by (rule zenon_and_1 [OF z_Him])
    have z_Hip: "?z_hip" (is "?z_heo<=>?z_hfm")
    by (rule zenon_and_0 [OF z_Hio])
    show FALSE
    proof (rule zenon_equiv [OF z_Hip])
     assume z_Hen:"(~?z_heo)" (is "~~?z_heq")
     assume z_His:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=''Done'')" (is "?z_hfe~=?z_hbh")
     show FALSE
     by (rule zenon_L2_ [OF z_Hen z_Hdx z_Hep])
    next
     assume z_Heo:"?z_heo" (is "?z_heh~=_")
     assume z_Hfm:"?z_hfm" (is "?z_hfe=?z_hbh")
     show FALSE
     by (rule zenon_L4_ [OF z_Hi z_Hfm z_Hff])
    qed
   qed
  next
   assume z_Hfr:"(a_CONSTANTunde_punde_1unde_a \\in ?z_hfp)" (is "?z_hfr")
   assume z_Hgl:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_1unde_a)"
   assume z_Hig:"(?z_heg~=(a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_1unde_a]))" (is "_~=?z_hih")
   have z_Hij: "?z_hii(a_CONSTANTunde_punde_1unde_a)" (is "_=>?z_hik")
   by (rule zenon_all_0 [of "?z_hii" "a_CONSTANTunde_punde_1unde_a", OF z_Hhj])
   show FALSE
   proof (rule zenon_imply [OF z_Hij])
    assume z_Hfz:"(~?z_hd)"
    show FALSE
    by (rule notE [OF z_Hfz z_Hd])
   next
    assume z_Hik:"?z_hik" (is "?z_hil&?z_him")
    have z_Him: "?z_him" (is "?z_hin&?z_hio")
    by (rule zenon_and_1 [OF z_Hik])
    have z_Hio: "?z_hio" (is "?z_hip&?z_hiq")
    by (rule zenon_and_1 [OF z_Him])
    have z_Hip: "?z_hip" (is "?z_heo<=>?z_hfm")
    by (rule zenon_and_0 [OF z_Hio])
    have z_Hiq: "?z_hiq" (is "_=>?z_hir")
    by (rule zenon_and_1 [OF z_Hio])
    show FALSE
    proof (rule zenon_equiv [OF z_Hip])
     assume z_Hen:"(~?z_heo)" (is "~~?z_heq")
     assume z_His:"((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_1unde_a])~=''Done'')" (is "?z_hfe~=?z_hbh")
     show FALSE
     by (rule zenon_L2_ [OF z_Hen z_Hdx z_Hep])
    next
     assume z_Heo:"?z_heo" (is "?z_heh~=_")
     assume z_Hfm:"?z_hfm" (is "?z_hfe=?z_hbh")
     show FALSE
     proof (rule zenon_imply [OF z_Hiq])
      assume z_Hen:"(~?z_heo)" (is "~~?z_heq")
      show FALSE
      by (rule notE [OF z_Hen z_Heo])
     next
      assume z_Hir:"?z_hir"
      show FALSE
      proof (rule notE [OF z_Hig])
       have z_Her: "(?z_heh=?z_heg)"
       proof (rule zenon_nnpp [of "(?z_heh=?z_heg)"])
        assume z_Hes:"(?z_heh~=?z_heg)"
        show FALSE
        proof (rule zenon_em [of "(?z_heg=?z_heg)"])
         assume z_Het:"(?z_heg=?z_heg)"
         show FALSE
         proof (rule notE [OF z_Hes])
          have z_Heu: "(?z_heg=?z_heh)"
          proof (rule zenon_nnpp [of "(?z_heg=?z_heh)"])
           assume z_Hef:"(?z_heg~=?z_heh)"
           show FALSE
           by (rule zenon_L1_ [OF z_Hef z_Hdx])
          qed
          have z_Her: "(?z_heh=?z_heg)"
          by (rule subst [where P="(\<lambda>zenon_Vgfca. (zenon_Vgfca=?z_heg))", OF z_Heu], fact z_Het)
          thus "(?z_heh=?z_heg)" .
         qed
        next
         assume z_Hey:"(?z_heg~=?z_heg)"
         show FALSE
         by (rule zenon_noteq [OF z_Hey])
        qed
       qed
       have z_Hjt: "(?z_heg=?z_hih)"
       by (rule subst [where P="(\<lambda>zenon_Vlfca. (zenon_Vlfca=?z_hih))", OF z_Her], fact z_Hir)
       thus "(?z_heg=?z_hih)" .
      qed
     qed
    qed
   qed
  next
   assume z_Hfq:"(~(a_CONSTANTunde_punde_1unde_a \\in ?z_hfp))" (is "~?z_hfr")
   show FALSE
   by (rule zenon_L5_ [OF z_Hfo z_Hfq z_Hd])
  qed
 next
  assume z_Hlq:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hlr")
  assume z_Hdz:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hea&?z_hec")
  have z_Hea: "?z_hea" (is "_=?z_heb")
  by (rule zenon_and_0 [OF z_Hdz])
  have z_Hgm: "(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (?z_hdm[a_CONSTANTunde_punde_a])))" (is "_=?z_hgn")
  by (rule subst [where P="(\<lambda>zenon_Vafca. (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (zenon_Vafca[a_CONSTANTunde_punde_a]))))", OF z_Hj z_Hea])
  have z_Hlx: "(~((?z_hdd[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hma")
  by (rule subst [where P="(\<lambda>zenon_Vcfca. (~((zenon_Vcfca[a_CONSTANTunde_punde_a])~={})))", OF z_Hk z_Hlq])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vkd. (~(zenon_Vkd~={})))" "a_VARIABLEunde_notKnownunde_a" "a_CONSTANTunde_punde_a" "subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))" "a_CONSTANTunde_punde_a", OF z_Hlx])
   assume z_Hkm:"(a_CONSTANTunde_punde_a \\in ?z_hkn)" (is "?z_hkm")
   assume z_Hke:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_a)"
   assume z_Hmk:"(~(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))~={}))" (is "~~?z_hmm")
   have z_Hmn: "(~(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((?z_hdm[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))~={}))" (is "~~?z_hms")
   by (rule subst [where P="(\<lambda>zenon_Vefca. (~(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((zenon_Vefca[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))~={})))", OF z_Hj z_Hmk])
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vesf. (~(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a(zenon_Vesf)), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))~={})))" "a_VARIABLEunde_knownunde_a" "a_CONSTANTunde_punde_a" "((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))" "a_CONSTANTunde_punde_a", OF z_Hmn])
    assume z_Hjz:"(a_CONSTANTunde_punde_a \\in ?z_hfp)" (is "?z_hjz")
    assume z_Hke:"(a_CONSTANTunde_punde_a=a_CONSTANTunde_punde_a)"
    assume z_Hni:"(~(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a(((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))~={}))" (is "~~?z_hnn")
    show FALSE
    by (rule zenon_L9_ [OF z_Hjx z_Hfo z_Hep z_Hhj z_Hgm z_Hjz z_Hd z_Hgk])
   next
    assume z_Hjz:"(a_CONSTANTunde_punde_a \\in ?z_hfp)" (is "?z_hjz")
    assume z_Hkg:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_a)"
    assume z_Hno:"(~(subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))~={}))" (is "~~?z_hns")
    show FALSE
    by (rule zenon_noteq [OF z_Hkg])
   next
    assume z_Hki:"(~(a_CONSTANTunde_punde_a \\in ?z_hfp))" (is "~?z_hjz")
    show FALSE
    by (rule zenon_L10_ [OF z_Hfo z_Hki z_Hc])
   qed
  next
   assume z_Hkm:"(a_CONSTANTunde_punde_a \\in ?z_hkn)" (is "?z_hkm")
   assume z_Hkg:"(a_CONSTANTunde_punde_a~=a_CONSTANTunde_punde_a)"
   assume z_Hnt:"(~((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={}))" (is "~~?z_hnu")
   show FALSE
   by (rule zenon_noteq [OF z_Hkg])
  next
   assume z_Hkl:"(~(a_CONSTANTunde_punde_a \\in ?z_hkn))" (is "~?z_hkm")
   show FALSE
   by (rule zenon_L12_ [OF z_Hgm z_Hc z_Hfo z_Hko z_Hkl])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 220"; *} qed
lemma ob'229:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'51: "(((((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_InvBunde_a))) \<and> (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))), ((0))))) \<Rightarrow> (\<forall> a_CONSTANTunde_Punde_a \<in> (a_STATEunde_PA1unde_a) : (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))))))))) | (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))))))))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'52: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'68: "((\<And> a_CONSTANTunde_qunde_a :: c. a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a) \<Longrightarrow> (((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a)))))), ((0))))) \<Longrightarrow> (\<And> a_CONSTANTunde_Punde_a :: c. a_CONSTANTunde_Punde_a \<in> ((h003cd :: c)) \<Longrightarrow> (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))))))))) | (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a))))))))))))))"
shows "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1)))))), ((0))))) \<Rightarrow> (\<forall> a_CONSTANTunde_Punde_a \<in> ((h003cd :: c)) : (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))))))))) | (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a))))))))))))))"(is "PROP ?ob'229")
proof -
ML_command {* writeln "*** TLAPS ENTER 229"; *}
show "PROP ?ob'229"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_435e04.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_435e04.znn.out
;; obligation #229
$hyp "v'51" (/\ (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_InvBunde_a)
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)))
(TLA.bAll a_STATEunde_PA1unde_a ((a_CONSTANTunde_Punde_a) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))))))))
a_STATEunde_GFXCorrectunde_a)
$hyp "v'52" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'68" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_qunde_a) (=> (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a))) (TLA.bAll h003cd ((a_CONSTANTunde_Punde_a) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a)))))))))))
$goal (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (=> (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a_1)))
(TLA.bAll h003cd ((a_CONSTANTunde_Punde_a) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a_1))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a)))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_qunde_a. ((0 < a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a])))=>bAll(h003cd, (\<lambda>a_CONSTANTunde_Punde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a])) < a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_Punde_a[a_CONSTANTunde_iunde_a]))))))|((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a]) \\subseteq UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_Punde_a[a_CONSTANTunde_iunde_a])))))))))))" (is "?z_hd")
 using v'68 by blast
 assume z_He:"(~?z_hd)"
 show FALSE
 by (rule notE [OF z_He z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 229"; *} qed
lemma ob'571:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'52: "(((((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_InvBunde_a))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'53: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'70: "((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a)))))), ((0)))))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h003cd :: c)))"
assumes v'74: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'75: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
fixes a_CONSTANTunde_waunde_a
assumes a_CONSTANTunde_waunde_a_in : "(a_CONSTANTunde_waunde_a \<in> (a_STATEunde_WriterAssignmentunde_a))"
assumes v'93: "(((a_CONSTANTunde_Punde_a) = ((a_STATEunde_PVunde_a ((a_CONSTANTunde_waunde_a))))))"
(* usable definition ACTION_C_ suppressed *)
(* usable definition ACTION_SS_ suppressed *)
(* usable definition CONSTANT_TT_ suppressed *)
(* usable definition CONSTANT_UU_ suppressed *)
(* usable definition CONSTANT_f_ suppressed *)
assumes v'116: "((((a_ACTIONunde_Cunde_a) \<in> (Nat))) & (((a_ACTIONunde_SSunde_a) \<subseteq> (Nat))) & ((a_CONSTANTunde_IsFiniteSetunde_a ((a_ACTIONunde_SSunde_a)))))"
assumes v'117: "((((a_CONSTANTunde_Cardinalityunde_a ((a_ACTIONunde_SSunde_a)))) = ((arith_add ((a_ACTIONunde_Cunde_a), ((Succ[0])))))))"
assumes v'118: "((((a_CONSTANTunde_TTunde_a) \<subseteq> (a_CONSTANTunde_UUunde_a))) & ((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_UUunde_a)))) & ((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_TTunde_a)))))"
assumes v'119: "(((a_CONSTANTunde_funde_a) \<in> ([(a_ACTIONunde_SSunde_a) \<rightarrow> (a_CONSTANTunde_TTunde_a)])))"
assumes v'120: "(\<forall> a_CONSTANTunde_xunde_a \<in> (a_ACTIONunde_SSunde_a) : (\<forall> a_CONSTANTunde_yunde_a \<in> (a_ACTIONunde_SSunde_a) : (((((a_CONSTANTunde_xunde_a) \<noteq> (a_CONSTANTunde_yunde_a))) \<Rightarrow> (((fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))) \<noteq> (fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_yunde_a)))))))))"
assumes v'121: "(\<forall>a_CONSTANTunde_Sunde_a : (\<forall>a_CONSTANTunde_Tunde_a : (\<forall>a_CONSTANTunde_funde_a_1 : (((((((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_Sunde_a)))) \<and> ((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_Tunde_a)))))) & (((a_CONSTANTunde_funde_a_1) \<in> ([(a_CONSTANTunde_Sunde_a) \<rightarrow> (a_CONSTANTunde_Tunde_a)]))) & (\<forall> a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Sunde_a) : (\<forall> a_CONSTANTunde_yunde_a \<in> (a_CONSTANTunde_Sunde_a) : (((((a_CONSTANTunde_xunde_a) \<noteq> (a_CONSTANTunde_yunde_a))) \<Rightarrow> (((fapply ((a_CONSTANTunde_funde_a_1), (a_CONSTANTunde_xunde_a))) \<noteq> (fapply ((a_CONSTANTunde_funde_a_1), (a_CONSTANTunde_yunde_a)))))))))) \<Rightarrow> ((leq (((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_Sunde_a)))), ((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_Tunde_a))))))))))))"
shows "((leq (((a_CONSTANTunde_Cardinalityunde_a ((a_ACTIONunde_SSunde_a)))), ((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_TTunde_a)))))))"(is "PROP ?ob'571")
proof -
ML_command {* writeln "*** TLAPS ENTER 571"; *}
show "PROP ?ob'571"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_f80467.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_f80467.znn.out
;; obligation #571
$hyp "v'52" (/\ (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_InvBunde_a)
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'53" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "v'70" (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)))
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h003cd)
$hyp "v'74" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'75" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$hyp "a_CONSTANTunde_waunde_a_in" (TLA.in a_CONSTANTunde_waunde_a a_STATEunde_WriterAssignmentunde_a)
$hyp "v'93" (= a_CONSTANTunde_Punde_a
(a_STATEunde_PVunde_a a_CONSTANTunde_waunde_a))
$hyp "v'116" (/\ (TLA.in a_ACTIONunde_Cunde_a arith.N)
(TLA.subseteq a_ACTIONunde_SSunde_a arith.N)
(a_CONSTANTunde_IsFiniteSetunde_a a_ACTIONunde_SSunde_a))
$hyp "v'117" (= (a_CONSTANTunde_Cardinalityunde_a a_ACTIONunde_SSunde_a)
(arith.add a_ACTIONunde_Cunde_a
(TLA.fapply TLA.Succ 0)))
$hyp "v'118" (/\ (TLA.subseteq a_CONSTANTunde_TTunde_a
a_CONSTANTunde_UUunde_a)
(a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_UUunde_a)
(a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_TTunde_a))
$hyp "v'119" (TLA.in a_CONSTANTunde_funde_a
(TLA.FuncSet a_ACTIONunde_SSunde_a a_CONSTANTunde_TTunde_a))
$hyp "v'120" (TLA.bAll a_ACTIONunde_SSunde_a ((a_CONSTANTunde_xunde_a) (TLA.bAll a_ACTIONunde_SSunde_a ((a_CONSTANTunde_yunde_a) (=> (-. (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a))
(-. (= (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a)
(TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_yunde_a))))))))
$hyp "v'121" (A. ((a_CONSTANTunde_Sunde_a) (A. ((a_CONSTANTunde_Tunde_a) (A. ((a_CONSTANTunde_funde_a_1) (=> (/\ (/\ (a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_Sunde_a)
(a_CONSTANTunde_IsFiniteSetunde_a a_CONSTANTunde_Tunde_a))
(TLA.in a_CONSTANTunde_funde_a_1
(TLA.FuncSet a_CONSTANTunde_Sunde_a a_CONSTANTunde_Tunde_a))
(TLA.bAll a_CONSTANTunde_Sunde_a ((a_CONSTANTunde_xunde_a) (TLA.bAll a_CONSTANTunde_Sunde_a ((a_CONSTANTunde_yunde_a) (=> (-. (= a_CONSTANTunde_xunde_a
a_CONSTANTunde_yunde_a))
(-. (= (TLA.fapply a_CONSTANTunde_funde_a_1 a_CONSTANTunde_xunde_a)
(TLA.fapply a_CONSTANTunde_funde_a_1 a_CONSTANTunde_yunde_a)))))))))
(arith.le (a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_Sunde_a)
(a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_Tunde_a)))))))))
$goal (arith.le (a_CONSTANTunde_Cardinalityunde_a a_ACTIONunde_SSunde_a)
(a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_TTunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hk:"((a_ACTIONunde_Cunde_a \\in Nat)&((a_ACTIONunde_SSunde_a \\subseteq Nat)&a_CONSTANTunde_IsFiniteSetunde_a(a_ACTIONunde_SSunde_a)))" (is "?z_hr&?z_hu")
 using v'116 by blast
 have z_Hm:"((a_CONSTANTunde_TTunde_a \\subseteq a_CONSTANTunde_UUunde_a)&(a_CONSTANTunde_IsFiniteSetunde_a(a_CONSTANTunde_UUunde_a)&a_CONSTANTunde_IsFiniteSetunde_a(a_CONSTANTunde_TTunde_a)))" (is "?z_hy&?z_hbb")
 using v'118 by blast
 have z_Hp:"(\\A a_CONSTANTunde_Sunde_a:(\\A a_CONSTANTunde_Tunde_a:(\\A a_CONSTANTunde_funde_a_1:(((a_CONSTANTunde_IsFiniteSetunde_a(a_CONSTANTunde_Sunde_a)&a_CONSTANTunde_IsFiniteSetunde_a(a_CONSTANTunde_Tunde_a))&((a_CONSTANTunde_funde_a_1 \\in FuncSet(a_CONSTANTunde_Sunde_a, a_CONSTANTunde_Tunde_a))&bAll(a_CONSTANTunde_Sunde_a, (\<lambda>a_CONSTANTunde_xunde_a. bAll(a_CONSTANTunde_Sunde_a, (\<lambda>a_CONSTANTunde_yunde_a. ((a_CONSTANTunde_xunde_a~=a_CONSTANTunde_yunde_a)=>((a_CONSTANTunde_funde_a_1[a_CONSTANTunde_xunde_a])~=(a_CONSTANTunde_funde_a_1[a_CONSTANTunde_yunde_a])))))))))=>(a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Sunde_a) <= a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Tunde_a))))))" (is "\\A x : ?z_hcf(x)")
 using v'121 by blast
 have z_Hn:"(a_CONSTANTunde_funde_a \\in FuncSet(a_ACTIONunde_SSunde_a, a_CONSTANTunde_TTunde_a))" (is "?z_hn")
 using v'119 by blast
 have z_Ho:"bAll(a_ACTIONunde_SSunde_a, (\<lambda>a_CONSTANTunde_xunde_a. bAll(a_ACTIONunde_SSunde_a, (\<lambda>a_CONSTANTunde_yunde_a. ((a_CONSTANTunde_xunde_a~=a_CONSTANTunde_yunde_a)=>((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])~=(a_CONSTANTunde_funde_a[a_CONSTANTunde_yunde_a])))))))" (is "?z_ho")
 using v'120 by blast
 assume z_Hq:"(~(a_CONSTANTunde_Cardinalityunde_a(a_ACTIONunde_SSunde_a) <= a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_TTunde_a)))" (is "~?z_hcp")
 have z_Hu: "?z_hu" (is "?z_hv&?z_hx")
 by (rule zenon_and_1 [OF z_Hk])
 have z_Hx: "?z_hx"
 by (rule zenon_and_1 [OF z_Hu])
 have z_Hbb: "?z_hbb" (is "?z_hbc&?z_hbd")
 by (rule zenon_and_1 [OF z_Hm])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_1 [OF z_Hbb])
 have z_Hcs: "?z_hcf(a_ACTIONunde_SSunde_a)" (is "\\A x : ?z_hct(x)")
 by (rule zenon_all_0 [of "?z_hcf" "a_ACTIONunde_SSunde_a", OF z_Hp])
 have z_Hcu: "?z_hct(a_CONSTANTunde_TTunde_a)" (is "\\A x : ?z_hcv(x)")
 by (rule zenon_all_0 [of "?z_hct" "a_CONSTANTunde_TTunde_a", OF z_Hcs])
 have z_Hcw: "?z_hcv(a_CONSTANTunde_funde_a)" (is "?z_hcx=>_")
 by (rule zenon_all_0 [of "?z_hcv" "a_CONSTANTunde_funde_a", OF z_Hcu])
 show FALSE
 proof (rule zenon_imply [OF z_Hcw])
  assume z_Hcy:"(~?z_hcx)" (is "~(?z_hcz&?z_hda)")
  show FALSE
  proof (rule zenon_notand [OF z_Hcy])
   assume z_Hdb:"(~?z_hcz)"
   show FALSE
   proof (rule zenon_notand [OF z_Hdb])
    assume z_Hdc:"(~?z_hx)"
    show FALSE
    by (rule notE [OF z_Hdc z_Hx])
   next
    assume z_Hdd:"(~?z_hbd)"
    show FALSE
    by (rule notE [OF z_Hdd z_Hbd])
   qed
  next
   assume z_Hde:"(~?z_hda)"
   show FALSE
   proof (rule zenon_notand [OF z_Hde])
    assume z_Hdf:"(~?z_hn)"
    show FALSE
    by (rule notE [OF z_Hdf z_Hn])
   next
    assume z_Hdg:"(~?z_ho)"
    show FALSE
    by (rule notE [OF z_Hdg z_Ho])
   qed
  qed
 next
  assume z_Hcp:"?z_hcp"
  show FALSE
  by (rule notE [OF z_Hq z_Hcp])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 571"; *} qed
lemma ob'582:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'51: "(((((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_InvBunde_a))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'52: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'71: "((((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) \<Longrightarrow> ((a_h5e3f2a :: c))))"
assumes v'72: "(((((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({}))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))) & ((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))) \<Longrightarrow> ((a_h5e3f2a :: c))))"
assumes v'73: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'74: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'75: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'76: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'77: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
shows "((a_h5e3f2a :: c))"(is "PROP ?ob'582")
proof -
ML_command {* writeln "*** TLAPS ENTER 582"; *}
show "PROP ?ob'582"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_77039f.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_77039f.znn.out
;; obligation #582
$hyp "v'51" (/\ (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_InvBunde_a)
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'52" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'71" (=> (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a) a_h5e3f2a)
$hyp "v'72" (=> (/\ (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset) (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))
(= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)) a_h5e3f2a)
$hyp "v'73" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'74" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'75" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'76" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'77" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$goal a_h5e3f2a
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hj:"(a_VARIABLEunde_A1unde_hash_primea=a_VARIABLEunde_A1unde_a)"
 using v'77 by blast
 have z_Hi:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_ho")
 using v'76 by blast
 have z_Hh:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hbb")
 using v'75 by blast
 have z_Hd:"((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)=>a_h5e3f2a)" (is "?z_hbj=>_")
 using v'71 by blast
 have z_Hf:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hf")
 using v'73 by blast
 have z_He:"(((a_VARIABLEunde_knownunde_hash_primea=?z_hbb)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_ho)&(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})&((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))&(a_VARIABLEunde_A1unde_hash_primea=a_VARIABLEunde_A1unde_a))))))=>a_h5e3f2a)" (is "?z_hcc=>_")
 using v'72 by blast
 have zenon_L1_: "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj) ==> (a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hbq ==> ?z_hci ==> FALSE")
 proof -
  assume z_Hbq:"?z_hbq" (is "?z_hbr&_")
  assume z_Hci:"?z_hci"
  have z_Hbj: "?z_hbj"
  by (rule zenon_and_1 [OF z_Hbq])
  show FALSE
  by (rule notE [OF z_Hci z_Hbj])
 qed
 assume z_Hk:"(~a_h5e3f2a)"
 show FALSE
 proof (rule zenon_imply [OF z_Hd])
  assume z_Hci:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
  show FALSE
  proof (rule zenon_imply [OF z_He])
   assume z_Hcj:"(~?z_hcc)" (is "~(?z_hh&?z_hcd)")
   show FALSE
   proof (rule zenon_notand [OF z_Hcj])
    assume z_Hck:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbb)"
    show FALSE
    by (rule notE [OF z_Hck z_Hh])
   next
    assume z_Hcl:"(~?z_hcd)" (is "~(?z_hi&?z_hce)")
    show FALSE
    proof (rule zenon_notand [OF z_Hcl])
     assume z_Hcm:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_ho)"
     show FALSE
     by (rule notE [OF z_Hcm z_Hi])
    next
     assume z_Hcn:"(~?z_hce)" (is "~(?z_hcf&?z_hcg)")
     show FALSE
     proof (rule zenon_notand [OF z_Hcn])
      assume z_Hbn:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hbo~=_")
      show FALSE
      proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(?z_hbo~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj)" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hf])
       assume z_Hbn:"(?z_hbo~={})"
       assume z_Hbq:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj)" (is "?z_hbr&_")
       show FALSE
       by (rule zenon_L1_ [OF z_Hbq z_Hci])
      next
       assume z_Hcq:"(~(?z_hbo~={}))"
       assume z_Hbw:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hbx&?z_hbz")
       show FALSE
       by (rule notE [OF z_Hcq z_Hbn])
      qed
     next
      assume z_Hcr:"(~?z_hcg)" (is "~(?z_hbx&?z_hch)")
      show FALSE
      proof (rule zenon_notand [OF z_Hcr])
       assume z_Hcs:"(a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hby")
       show FALSE
       proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj)" "(?z_hbx&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hf])
        assume z_Hbn:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hbo~=_")
        assume z_Hbq:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj)" (is "?z_hbr&_")
        show FALSE
        by (rule zenon_L1_ [OF z_Hbq z_Hci])
       next
        assume z_Hcq:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))"
        assume z_Hbw:"(?z_hbx&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "_&?z_hbz")
        have z_Hbx: "?z_hbx"
        by (rule zenon_and_0 [OF z_Hbw])
        show FALSE
        by (rule notE [OF z_Hcs z_Hbx])
       qed
      next
       assume z_Hct:"(~?z_hch)" (is "~(?z_hbz&?z_hj)")
       show FALSE
       proof (rule zenon_notand [OF z_Hct])
        assume z_Hcu:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_~=?z_hca")
        show FALSE
        proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj)" "(?z_hbx&?z_hbz)", OF z_Hf])
         assume z_Hbn:"((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})" (is "?z_hbo~=_")
         assume z_Hbq:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&?z_hbj)" (is "?z_hbr&_")
         show FALSE
         by (rule zenon_L1_ [OF z_Hbq z_Hci])
        next
         assume z_Hcq:"(~((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}))"
         assume z_Hbw:"(?z_hbx&?z_hbz)"
         have z_Hbz: "?z_hbz"
         by (rule zenon_and_1 [OF z_Hbw])
         show FALSE
         by (rule notE [OF z_Hcu z_Hbz])
        qed
       next
        assume z_Hcv:"(a_VARIABLEunde_A1unde_hash_primea~=a_VARIABLEunde_A1unde_a)"
        show FALSE
        by (rule notE [OF z_Hcv z_Hj])
       qed
      qed
     qed
    qed
   qed
  next
   assume z_Hbm:"a_h5e3f2a"
   show FALSE
   by (rule notE [OF z_Hk z_Hbm])
  qed
 next
  assume z_Hbm:"a_h5e3f2a"
  show FALSE
  by (rule notE [OF z_Hk z_Hbm])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 582"; *} qed
lemma ob'708:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'51: "(((((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_InvBunde_a))) \<and> (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a)))))), ((0))))) \<Rightarrow> (\<forall> a_CONSTANTunde_Punde_a \<in> (a_STATEunde_PA1unde_a) : (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))))))))) | (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))))))))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'52: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'66: "((a_ACTIONunde_bunde_a ((a_CONSTANTunde_punde_a))))"
assumes v'70: "((\<And> a_CONSTANTunde_qunde_a :: c. a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a) \<Longrightarrow> (((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a)))))), ((0))))) \<Longrightarrow> (\<And> a_CONSTANTunde_Punde_a :: c. a_CONSTANTunde_Punde_a \<in> ((h003cd :: c)) \<Longrightarrow> (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))))))))) | (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a))))))))))))))"
shows "(\<forall> a_CONSTANTunde_punde_a_1 \<in> (a_CONSTANTunde_Procunde_a) : ((((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1)))))), ((0))))) \<Rightarrow> (\<forall> a_CONSTANTunde_Punde_a \<in> ((h003cd :: c)) : (((greater (((a_CONSTANTunde_Cardinalityunde_a (((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a)))))))))), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))))))))) | (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_punde_a_1))) \<subseteq> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_CONSTANTunde_Punde_a), (a_CONSTANTunde_iunde_a))))))))))))))"(is "PROP ?ob'708")
proof -
ML_command {* writeln "*** TLAPS ENTER 708"; *}
show "PROP ?ob'708"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_cd7154.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_cd7154.znn.out
;; obligation #708
$hyp "v'51" (/\ (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_InvBunde_a)
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)))
(TLA.bAll a_STATEunde_PA1unde_a ((a_CONSTANTunde_Punde_a) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))))))))
a_STATEunde_GFXCorrectunde_a)
$hyp "v'52" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'66" (a_ACTIONunde_bunde_a a_CONSTANTunde_punde_a)
$hyp "v'70" (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_qunde_a) (=> (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a))) (TLA.bAll h003cd ((a_CONSTANTunde_Punde_a) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a)))))))))))
$goal (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a_1) (=> (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a_1)))
(TLA.bAll h003cd ((a_CONSTANTunde_Punde_a) (\/ (arith.lt (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a_1))
(a_CONSTANTunde_Cardinalityunde_a (TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a))))))
(TLA.subseteq (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_punde_a_1)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_CONSTANTunde_Punde_a a_CONSTANTunde_iunde_a)))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_qunde_a. ((0 < a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a])))=>bAll(h003cd, (\<lambda>a_CONSTANTunde_Punde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a])) < a_CONSTANTunde_Cardinalityunde_a(UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_Punde_a[a_CONSTANTunde_iunde_a]))))))|((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_qunde_a]) \\subseteq UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_CONSTANTunde_Punde_a[a_CONSTANTunde_iunde_a])))))))))))" (is "?z_he")
 using v'70 by blast
 assume z_Hf:"(~?z_he)"
 show FALSE
 by (rule notE [OF z_Hf z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 708"; *} qed
lemma ob'721:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'51: "(((((((a_STATEunde_TypeOKunde_a) \<and> (a_STATEunde_InvBunde_a))) \<and> (a_STATEunde_InvCunde_a))) \<and> (a_STATEunde_GFXCorrectunde_a)))"
assumes v'52: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'66: "(\<exists> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A1unde_hash_primea :: c)) = ([(a_VARIABLEunde_A1unde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"
assumes v'67: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b'')))"
assumes v'68: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''a'')])))"
assumes v'69: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'70: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = (a_VARIABLEunde_knownunde_a)))"
assumes v'71: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = (a_VARIABLEunde_notKnownunde_a)))"
fixes a_CONSTANTunde_qunde_a
assumes a_CONSTANTunde_qunde_a_in : "(a_CONSTANTunde_qunde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'76: "((greater (((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_qunde_a)))))), ((0)))))"
fixes a_CONSTANTunde_Punde_a
assumes a_CONSTANTunde_Punde_a_in : "(a_CONSTANTunde_Punde_a \<in> ((h003cd :: c)))"
fixes a_CONSTANTunde_waunde_a
assumes a_CONSTANTunde_waunde_a_in : "(a_CONSTANTunde_waunde_a \<in> ((a_h68829a :: c)))"
assumes v'84: "(((a_CONSTANTunde_Punde_a) = ((h6db5c ((a_CONSTANTunde_waunde_a)) :: c))))"
shows "(\<exists> a_CONSTANTunde_junde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A1unde_hash_primea :: c)) = ([(a_VARIABLEunde_A1unde_a) EXCEPT ![(a_CONSTANTunde_junde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"(is "PROP ?ob'721")
proof -
ML_command {* writeln "*** TLAPS ENTER 721"; *}
show "PROP ?ob'721"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_c12c4b.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_c12c4b.znn.out
;; obligation #721
$hyp "v'51" (/\ (/\ (/\ a_STATEunde_TypeOKunde_a a_STATEunde_InvBunde_a)
a_STATEunde_InvCunde_a)
a_STATEunde_GFXCorrectunde_a)
$hyp "v'52" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'66" (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (= a_VARIABLEunde_A1unde_hash_primea
(TLA.except a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
$hyp "v'67" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
$hyp "v'68" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "a"))
$hyp "v'69" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'70" (= a_VARIABLEunde_knownunde_hash_primea
a_VARIABLEunde_knownunde_a)
$hyp "v'71" (= a_VARIABLEunde_notKnownunde_hash_primea
a_VARIABLEunde_notKnownunde_a)
$hyp "a_CONSTANTunde_qunde_a_in" (TLA.in a_CONSTANTunde_qunde_a a_CONSTANTunde_Procunde_a)
$hyp "v'76" (arith.lt 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_qunde_a)))
$hyp "a_CONSTANTunde_Punde_a_in" (TLA.in a_CONSTANTunde_Punde_a h003cd)
$hyp "a_CONSTANTunde_waunde_a_in" (TLA.in a_CONSTANTunde_waunde_a a_h68829a)
$hyp "v'84" (= a_CONSTANTunde_Punde_a
(h6db5c a_CONSTANTunde_waunde_a))
$goal (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_junde_a) (= a_VARIABLEunde_A1unde_hash_primea
(TLA.except a_VARIABLEunde_A1unde_a a_CONSTANTunde_junde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bEx((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a]), (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_hash_primea=except(a_VARIABLEunde_A1unde_a, a_CONSTANTunde_iunde_a, (a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a])))))" (is "?z_hd")
 using v'66 by blast
 assume z_Ho:"(~?z_hd)"
 show FALSE
 by (rule notE [OF z_Ho z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 721"; *} qed
lemma ob'874:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition CONSTANT_ProcSet_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_PS!IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_PS!Cardinality_ suppressed *)
(* usable definition STATE_PS!vars_ suppressed *)
(* usable definition CONSTANT_PS!ProcSet_ suppressed *)
(* usable definition STATE_PS!Init_ suppressed *)
(* usable definition ACTION_PS!A_ suppressed *)
(* usable definition ACTION_PS!Pr_ suppressed *)
(* usable definition ACTION_PS!Next_ suppressed *)
(* usable definition TEMPORAL_PS!Spec_ suppressed *)
(* usable definition STATE_PS!Termination_ suppressed *)
(* usable definition STATE_PS!TypeOK_ suppressed *)
(* usable definition STATE_PS!Done_ suppressed *)
(* usable definition STATE_PS!GFXCorrect_ suppressed *)
assumes v'64: "(a_STATEunde_Invunde_a)"
assumes v'65: "((hdb2fe :: c))"
assumes v'66: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'74: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'77: "(((((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a))) & ((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))) \<Longrightarrow> (((a_ACTIONunde_PSexcl_Nextunde_a) \<or> ((((hce00c :: c)) = (a_STATEunde_PSexcl_varsunde_a)))))))"
assumes v'78: "(((((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))]))) & ((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))]))) & (((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({}))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))) & ((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))) \<Longrightarrow> (((a_ACTIONunde_PSexcl_Nextunde_a) \<or> ((((hce00c :: c)) = (a_STATEunde_PSexcl_varsunde_a)))))))"
assumes v'79: "(cond((((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> ({}))), (((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''b'')]))) & ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))), (((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))]))) & ((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')]))))))"
assumes v'80: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'81: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'82: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'83: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
shows "(((a_ACTIONunde_PSexcl_Nextunde_a) \<or> ((((hce00c :: c)) = (a_STATEunde_PSexcl_varsunde_a)))))"(is "PROP ?ob'874")
proof -
ML_command {* writeln "*** TLAPS ENTER 874"; *}
show "PROP ?ob'874"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_ef4591.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_ef4591.znn.out
;; obligation #874
$hyp "v'64" a_STATEunde_Invunde_a
$hyp "v'65" hdb2fe
$hyp "v'66" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'74" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'77" (=> (/\ (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea a_VARIABLEunde_resultunde_a)
(= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)) (\/ a_ACTIONunde_PSexcl_Nextunde_a (= hce00c
a_STATEunde_PSexcl_varsunde_a)))
$hyp "v'78" (=> (/\ (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
(= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset) (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))
(= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)) (\/ a_ACTIONunde_PSexcl_Nextunde_a (= hce00c
a_STATEunde_PSexcl_varsunde_a)))
$hyp "v'79" (TLA.cond (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)) (/\ (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "b"))
(= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)) (/\ (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
(= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))))
$hyp "v'80" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'81" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'82" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'83" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$goal (\/ a_ACTIONunde_PSexcl_Nextunde_a (= hce00c
a_STATEunde_PSexcl_varsunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hk:"(a_VARIABLEunde_A1unde_hash_primea=a_VARIABLEunde_A1unde_a)"
 using v'83 by blast
 have z_Hj:"(a_VARIABLEunde_notKnownunde_hash_primea=except(a_VARIABLEunde_notKnownunde_a, a_CONSTANTunde_punde_a, subsetOf(isa'dotdot(0, a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))), (\<lambda>a_CONSTANTunde_iunde_a. ((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])~=(a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a]))))))" (is "_=?z_hp")
 using v'82 by blast
 have z_Hi:"(a_VARIABLEunde_knownunde_hash_primea=except(a_VARIABLEunde_knownunde_a, a_CONSTANTunde_punde_a, ((a_VARIABLEunde_knownunde_a[a_CONSTANTunde_punde_a]) \\cup UNION(setOfAll(Nat, (\<lambda>a_CONSTANTunde_iunde_a. (a_VARIABLEunde_A1unde_a[a_CONSTANTunde_iunde_a])))))))" (is "_=?z_hbc")
 using v'81 by blast
 have z_Hg:"(((a_VARIABLEunde_knownunde_hash_primea=?z_hbc)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hp)&(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])={})&((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))&(a_VARIABLEunde_A1unde_hash_primea=a_VARIABLEunde_A1unde_a))))))=>(a_ACTIONunde_PSexcl_Nextunde_a|(hce00c=a_STATEunde_PSexcl_varsunde_a)))" (is "?z_hbk=>?z_hcb")
 using v'78 by blast
 have z_Hh:"cond(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={}), ((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)), ((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))))" (is "?z_hh")
 using v'79 by blast
 have z_Hf:"(((a_VARIABLEunde_knownunde_hash_primea=?z_hbc)&((a_VARIABLEunde_notKnownunde_hash_primea=?z_hp)&(((a_VARIABLEunde_notKnownunde_hash_primea[a_CONSTANTunde_punde_a])~={})&((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&((a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)&(a_VARIABLEunde_A1unde_hash_primea=a_VARIABLEunde_A1unde_a))))))=>?z_hcb)" (is "?z_hcn=>_")
 using v'77 by blast
 have zenon_L1_: "(a_VARIABLEunde_knownunde_hash_primea=?z_hbc) ==> (a_VARIABLEunde_knownunde_hash_primea~=?z_hbc) ==> FALSE" (is "?z_hi ==> ?z_hcs ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hcs:"?z_hcs"
  show FALSE
  by (rule notE [OF z_Hcs z_Hi])
 qed
 have zenon_L2_: "(a_VARIABLEunde_notKnownunde_hash_primea=?z_hp) ==> (a_VARIABLEunde_notKnownunde_hash_primea~=?z_hp) ==> FALSE" (is "?z_hj ==> ?z_hct ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hct:"?z_hct"
  show FALSE
  by (rule notE [OF z_Hct z_Hj])
 qed
 have zenon_L3_: "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))) ==> (a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))) ==> FALSE" (is "?z_hcm ==> ?z_hcu ==> FALSE")
 proof -
  assume z_Hcm:"?z_hcm" (is "?z_hbr&?z_hbw")
  assume z_Hcu:"?z_hcu" (is "_~=?z_hbt")
  have z_Hbr: "?z_hbr"
  by (rule zenon_and_0 [OF z_Hcm])
  show FALSE
  by (rule notE [OF z_Hcu z_Hbr])
 qed
 have zenon_L4_: "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))) ==> (a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')) ==> FALSE" (is "?z_hcm ==> ?z_hcv ==> FALSE")
 proof -
  assume z_Hcm:"?z_hcm" (is "?z_hbr&?z_hbw")
  assume z_Hcv:"?z_hcv" (is "_~=?z_hby")
  have z_Hbw: "?z_hbw"
  by (rule zenon_and_1 [OF z_Hcm])
  show FALSE
  by (rule notE [OF z_Hcv z_Hbw])
 qed
 have zenon_L5_: "(a_VARIABLEunde_A1unde_hash_primea=a_VARIABLEunde_A1unde_a) ==> (a_VARIABLEunde_A1unde_hash_primea~=a_VARIABLEunde_A1unde_a) ==> FALSE" (is "?z_hk ==> ?z_hcw ==> FALSE")
 proof -
  assume z_Hk:"?z_hk"
  assume z_Hcw:"?z_hcw"
  show FALSE
  by (rule notE [OF z_Hcw z_Hk])
 qed
 have zenon_L6_: "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)) ==> (a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b'')) ==> FALSE" (is "?z_hch ==> ?z_hcx ==> FALSE")
 proof -
  assume z_Hch:"?z_hch" (is "?z_hci&?z_hcl")
  assume z_Hcx:"?z_hcx" (is "_~=?z_hcj")
  have z_Hci: "?z_hci"
  by (rule zenon_and_0 [OF z_Hch])
  show FALSE
  by (rule notE [OF z_Hcx z_Hci])
 qed
 have zenon_L7_: "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)) ==> (a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hch ==> ?z_hcy ==> FALSE")
 proof -
  assume z_Hch:"?z_hch" (is "?z_hci&?z_hcl")
  assume z_Hcy:"?z_hcy"
  have z_Hcl: "?z_hcl"
  by (rule zenon_and_1 [OF z_Hch])
  show FALSE
  by (rule notE [OF z_Hcy z_Hcl])
 qed
 assume z_Hl:"(~?z_hcb)" (is "~(_|?z_hcd)")
 have z_Hcz: "(~a_ACTIONunde_PSexcl_Nextunde_a)"
 by (rule zenon_notor_0 [OF z_Hl])
 have z_Hda: "(hce00c~=a_STATEunde_PSexcl_varsunde_a)"
 by (rule zenon_notor_1 [OF z_Hl])
 show FALSE
 proof (rule zenon_imply [OF z_Hf])
  assume z_Hdb:"(~?z_hcn)" (is "~(?z_hi&?z_hco)")
  show FALSE
  proof (rule zenon_notand [OF z_Hdb])
   assume z_Hcs:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbc)"
   show FALSE
   by (rule notE [OF z_Hcs z_Hi])
  next
   assume z_Hdc:"(~?z_hco)" (is "~(?z_hj&?z_hcp)")
   show FALSE
   proof (rule zenon_notand [OF z_Hdc])
    assume z_Hct:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hp)"
    show FALSE
    by (rule notE [OF z_Hct z_Hj])
   next
    assume z_Hdd:"(~?z_hcp)" (is "~(?z_hcg&?z_hcq)")
    show FALSE
    proof (rule zenon_notand [OF z_Hdd])
     assume z_Hde:"(~?z_hcg)" (is "~~?z_hbn")
     have z_Hbn: "?z_hbn" (is "?z_hbo=_")
     by (rule zenon_notnot_0 [OF z_Hde])
     show FALSE
     proof (rule zenon_imply [OF z_Hg])
      assume z_Hdf:"(~?z_hbk)" (is "~(_&?z_hbl)")
      show FALSE
      proof (rule zenon_notand [OF z_Hdf])
       assume z_Hcs:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbc)"
       show FALSE
       by (rule notE [OF z_Hcs z_Hi])
      next
       assume z_Hdg:"(~?z_hbl)" (is "~(_&?z_hbm)")
       show FALSE
       proof (rule zenon_notand [OF z_Hdg])
        assume z_Hct:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hp)"
        show FALSE
        by (rule notE [OF z_Hct z_Hj])
       next
        assume z_Hdh:"(~?z_hbm)" (is "~(_&?z_hbq)")
        show FALSE
        proof (rule zenon_notand [OF z_Hdh])
         assume z_Hcg:"?z_hcg"
         show FALSE
         by (rule notE [OF z_Hcg z_Hbn])
        next
         assume z_Hdi:"(~?z_hbq)" (is "~(?z_hbr&?z_hbv)")
         show FALSE
         proof (rule zenon_notand [OF z_Hdi])
          assume z_Hcu:"(a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hbt")
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "(?z_hbr&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hh])
           assume z_Hcg:"?z_hcg"
           assume z_Hch:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hci&?z_hcl")
           show FALSE
           by (rule notE [OF z_Hcg z_Hbn])
          next
           assume z_Hde:"(~?z_hcg)"
           assume z_Hcm:"(?z_hbr&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "_&?z_hbw")
           show FALSE
           by (rule zenon_L3_ [OF z_Hcm z_Hcu])
          qed
         next
          assume z_Hdl:"(~?z_hbv)" (is "~(?z_hbw&?z_hk)")
          show FALSE
          proof (rule zenon_notand [OF z_Hdl])
           assume z_Hcv:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_~=?z_hby")
           show FALSE
           proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "(?z_hbr&?z_hbw)", OF z_Hh])
            assume z_Hcg:"?z_hcg"
            assume z_Hch:"((a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "?z_hci&?z_hcl")
            show FALSE
            by (rule notE [OF z_Hcg z_Hbn])
           next
            assume z_Hde:"(~?z_hcg)"
            assume z_Hcm:"(?z_hbr&?z_hbw)"
            show FALSE
            by (rule zenon_L4_ [OF z_Hcm z_Hcv])
           qed
          next
           assume z_Hcw:"(a_VARIABLEunde_A1unde_hash_primea~=a_VARIABLEunde_A1unde_a)"
           show FALSE
           by (rule notE [OF z_Hcw z_Hk])
          qed
         qed
        qed
       qed
      qed
     next
      assume z_Hcb:"?z_hcb"
      show FALSE
      proof (rule zenon_or [OF z_Hcb])
       assume z_Hcc:"a_ACTIONunde_PSexcl_Nextunde_a"
       show FALSE
       by (rule notE [OF z_Hcz z_Hcc])
      next
       assume z_Hcd:"?z_hcd"
       show FALSE
       by (rule notE [OF z_Hda z_Hcd])
      qed
     qed
    next
     assume z_Hdm:"(~?z_hcq)" (is "~(?z_hci&?z_hcr)")
     show FALSE
     proof (rule zenon_notand [OF z_Hdm])
      assume z_Hcx:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''b''))" (is "_~=?z_hcj")
      show FALSE
      proof (rule zenon_imply [OF z_Hg])
       assume z_Hdf:"(~?z_hbk)" (is "~(_&?z_hbl)")
       show FALSE
       proof (rule zenon_notand [OF z_Hdf])
        assume z_Hcs:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbc)"
        show FALSE
        by (rule notE [OF z_Hcs z_Hi])
       next
        assume z_Hdg:"(~?z_hbl)" (is "~(_&?z_hbm)")
        show FALSE
        proof (rule zenon_notand [OF z_Hdg])
         assume z_Hct:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hp)"
         show FALSE
         by (rule notE [OF z_Hct z_Hj])
        next
         assume z_Hdh:"(~?z_hbm)" (is "~(?z_hbn&?z_hbq)")
         show FALSE
         proof (rule zenon_notand [OF z_Hdh])
          assume z_Hcg:"?z_hcg" (is "?z_hbo~=_")
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "(?z_hci&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hh])
           assume z_Hcg:"?z_hcg"
           assume z_Hch:"(?z_hci&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "_&?z_hcl")
           show FALSE
           by (rule zenon_L6_ [OF z_Hch z_Hcx])
          next
           assume z_Hde:"(~?z_hcg)"
           assume z_Hcm:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hbr&?z_hbw")
           show FALSE
           by (rule notE [OF z_Hde z_Hcg])
          qed
         next
          assume z_Hdi:"(~?z_hbq)" (is "~(?z_hbr&?z_hbv)")
          show FALSE
          proof (rule zenon_notand [OF z_Hdi])
           assume z_Hcu:"(a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hbt")
           show FALSE
           proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "(?z_hci&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "(?z_hbr&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hh])
            assume z_Hcg:"?z_hcg" (is "?z_hbo~=_")
            assume z_Hch:"(?z_hci&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "_&?z_hcl")
            show FALSE
            by (rule zenon_L6_ [OF z_Hch z_Hcx])
           next
            assume z_Hde:"(~?z_hcg)"
            assume z_Hcm:"(?z_hbr&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "_&?z_hbw")
            show FALSE
            by (rule zenon_L3_ [OF z_Hcm z_Hcu])
           qed
          next
           assume z_Hdl:"(~?z_hbv)" (is "~(?z_hbw&?z_hk)")
           show FALSE
           proof (rule zenon_notand [OF z_Hdl])
            assume z_Hcv:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_~=?z_hby")
            show FALSE
            proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "(?z_hci&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" "(?z_hbr&?z_hbw)", OF z_Hh])
             assume z_Hcg:"?z_hcg" (is "?z_hbo~=_")
             assume z_Hch:"(?z_hci&(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a))" (is "_&?z_hcl")
             show FALSE
             by (rule zenon_L6_ [OF z_Hch z_Hcx])
            next
             assume z_Hde:"(~?z_hcg)"
             assume z_Hcm:"(?z_hbr&?z_hbw)"
             show FALSE
             by (rule zenon_L4_ [OF z_Hcm z_Hcv])
            qed
           next
            assume z_Hcw:"(a_VARIABLEunde_A1unde_hash_primea~=a_VARIABLEunde_A1unde_a)"
            show FALSE
            by (rule notE [OF z_Hcw z_Hk])
           qed
          qed
         qed
        qed
       qed
      next
       assume z_Hcb:"?z_hcb"
       show FALSE
       proof (rule zenon_or [OF z_Hcb])
        assume z_Hcc:"a_ACTIONunde_PSexcl_Nextunde_a"
        show FALSE
        by (rule notE [OF z_Hcz z_Hcc])
       next
        assume z_Hcd:"?z_hcd"
        show FALSE
        by (rule notE [OF z_Hda z_Hcd])
       qed
      qed
     next
      assume z_Hdn:"(~?z_hcr)" (is "~(?z_hcl&?z_hk)")
      show FALSE
      proof (rule zenon_notand [OF z_Hdn])
       assume z_Hcy:"(a_VARIABLEunde_resultunde_hash_primea~=a_VARIABLEunde_resultunde_a)"
       show FALSE
       proof (rule zenon_imply [OF z_Hg])
        assume z_Hdf:"(~?z_hbk)" (is "~(_&?z_hbl)")
        show FALSE
        proof (rule zenon_notand [OF z_Hdf])
         assume z_Hcs:"(a_VARIABLEunde_knownunde_hash_primea~=?z_hbc)"
         show FALSE
         by (rule notE [OF z_Hcs z_Hi])
        next
         assume z_Hdg:"(~?z_hbl)" (is "~(_&?z_hbm)")
         show FALSE
         proof (rule zenon_notand [OF z_Hdg])
          assume z_Hct:"(a_VARIABLEunde_notKnownunde_hash_primea~=?z_hp)"
          show FALSE
          by (rule notE [OF z_Hct z_Hj])
         next
          assume z_Hdh:"(~?z_hbm)" (is "~(?z_hbn&?z_hbq)")
          show FALSE
          proof (rule zenon_notand [OF z_Hdh])
           assume z_Hcg:"?z_hcg" (is "?z_hbo~=_")
           show FALSE
           proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "(?z_hci&?z_hcl)" "((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hh])
            assume z_Hcg:"?z_hcg"
            assume z_Hch:"(?z_hci&?z_hcl)"
            show FALSE
            by (rule zenon_L7_ [OF z_Hch z_Hcy])
           next
            assume z_Hde:"(~?z_hcg)"
            assume z_Hcm:"((a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "?z_hbr&?z_hbw")
            show FALSE
            by (rule notE [OF z_Hde z_Hcg])
           qed
          next
           assume z_Hdi:"(~?z_hbq)" (is "~(?z_hbr&?z_hbv)")
           show FALSE
           proof (rule zenon_notand [OF z_Hdi])
            assume z_Hcu:"(a_VARIABLEunde_resultunde_hash_primea~=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_~=?z_hbt")
            show FALSE
            proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "(?z_hci&?z_hcl)" "(?z_hbr&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))", OF z_Hh])
             assume z_Hcg:"?z_hcg" (is "?z_hbo~=_")
             assume z_Hch:"(?z_hci&?z_hcl)"
             show FALSE
             by (rule zenon_L7_ [OF z_Hch z_Hcy])
            next
             assume z_Hde:"(~?z_hcg)"
             assume z_Hcm:"(?z_hbr&(a_VARIABLEunde_pcunde_hash_primea=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done'')))" (is "_&?z_hbw")
             show FALSE
             by (rule zenon_L3_ [OF z_Hcm z_Hcu])
            qed
           next
            assume z_Hdl:"(~?z_hbv)" (is "~(?z_hbw&_)")
            show FALSE
            proof (rule zenon_notand [OF z_Hdl])
             assume z_Hcv:"(a_VARIABLEunde_pcunde_hash_primea~=except(a_VARIABLEunde_pcunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_~=?z_hby")
             show FALSE
             proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "?z_hcg" "(?z_hci&?z_hcl)" "(?z_hbr&?z_hbw)", OF z_Hh])
              assume z_Hcg:"?z_hcg" (is "?z_hbo~=_")
              assume z_Hch:"(?z_hci&?z_hcl)"
              show FALSE
              by (rule zenon_L7_ [OF z_Hch z_Hcy])
             next
              assume z_Hde:"(~?z_hcg)"
              assume z_Hcm:"(?z_hbr&?z_hbw)"
              show FALSE
              by (rule zenon_L4_ [OF z_Hcm z_Hcv])
             qed
            next
             assume z_Hcw:"(a_VARIABLEunde_A1unde_hash_primea~=a_VARIABLEunde_A1unde_a)"
             show FALSE
             by (rule notE [OF z_Hcw z_Hk])
            qed
           qed
          qed
         qed
        qed
       next
        assume z_Hcb:"?z_hcb"
        show FALSE
        proof (rule zenon_or [OF z_Hcb])
         assume z_Hcc:"a_ACTIONunde_PSexcl_Nextunde_a"
         show FALSE
         by (rule notE [OF z_Hcz z_Hcc])
        next
         assume z_Hcd:"?z_hcd"
         show FALSE
         by (rule notE [OF z_Hda z_Hcd])
        qed
       qed
      next
       assume z_Hcw:"(a_VARIABLEunde_A1unde_hash_primea~=a_VARIABLEunde_A1unde_a)"
       show FALSE
       by (rule notE [OF z_Hcw z_Hk])
      qed
     qed
    qed
   qed
  qed
 next
  assume z_Hcb:"?z_hcb"
  show FALSE
  proof (rule zenon_or [OF z_Hcb])
   assume z_Hcc:"a_ACTIONunde_PSexcl_Nextunde_a"
   show FALSE
   by (rule notE [OF z_Hcz z_Hcc])
  next
   assume z_Hcd:"?z_hcd"
   show FALSE
   by (rule notE [OF z_Hda z_Hcd])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 874"; *} qed
lemma ob'885:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition CONSTANT_ProcSet_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_PS!IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_PS!Cardinality_ suppressed *)
(* usable definition STATE_PS!vars_ suppressed *)
(* usable definition CONSTANT_PS!ProcSet_ suppressed *)
(* usable definition STATE_PS!Init_ suppressed *)
(* usable definition TEMPORAL_PS!Spec_ suppressed *)
(* usable definition STATE_PS!Termination_ suppressed *)
(* usable definition STATE_PS!TypeOK_ suppressed *)
(* usable definition STATE_PS!Done_ suppressed *)
(* usable definition STATE_PS!GFXCorrect_ suppressed *)
assumes v'62: "(a_STATEunde_Invunde_a)"
assumes v'63: "((hdb2fe :: c))"
assumes v'64: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'72: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'81: "(\<forall>a_CONSTANTunde_xunde_a : ((((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_xunde_a)))) = ((a_CONSTANTunde_PSexcl_Cardinalityunde_a ((a_CONSTANTunde_xunde_a)))))))"
assumes v'82: "(((fapply ((a_STATEunde_pcBarunde_a), (a_CONSTANTunde_punde_a))) = (''A'')))"
assumes v'83: "(\<exists> a_CONSTANTunde_Punde_a \<in> (subsetOf(((SUBSET (a_CONSTANTunde_Procunde_a))), %a_CONSTANTunde_Qunde_a. ((((a_CONSTANTunde_punde_a) \<in> (a_CONSTANTunde_Qunde_a))) & (\<forall> a_CONSTANTunde_qunde_a \<in> (((a_CONSTANTunde_Procunde_a) \\ ({(a_CONSTANTunde_punde_a)}))) : (((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_qunde_a)))))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_Qunde_a)))))) | (((a_CONSTANTunde_Qunde_a) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_qunde_a)))))))))) : ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (a_CONSTANTunde_Punde_a)]))))"
assumes v'84: "((((a_h8b086a :: c)) = ([(a_STATEunde_pcBarunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')])))"
shows "(((((\<exists> a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((fapply ((a_STATEunde_pcBarunde_a), (a_CONSTANTunde_selfunde_a))) = (''A''))) & (\<exists> a_CONSTANTunde_Punde_a \<in> (subsetOf(((SUBSET (a_CONSTANTunde_Procunde_a))), %a_CONSTANTunde_Qunde_a. ((((a_CONSTANTunde_selfunde_a) \<in> (a_CONSTANTunde_Qunde_a))) & (\<forall> a_CONSTANTunde_punde_a_1 \<in> (((a_CONSTANTunde_Procunde_a) \\ ({(a_CONSTANTunde_selfunde_a)}))) : (((((a_CONSTANTunde_PSexcl_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a_1)))))) \<noteq> ((a_CONSTANTunde_PSexcl_Cardinalityunde_a ((a_CONSTANTunde_Qunde_a)))))) | (((a_CONSTANTunde_Qunde_a) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_punde_a_1)))))))))) : ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_selfunde_a)] = (a_CONSTANTunde_Punde_a)])))) & ((((a_h8b086a :: c)) = ([(a_STATEunde_pcBarunde_a) EXCEPT ![(a_CONSTANTunde_selfunde_a)] = (''Done'')]))))) \<or> (((\<forall> a_CONSTANTunde_selfunde_a \<in> (a_CONSTANTunde_PSexcl_ProcSetunde_a) : (((fapply ((a_STATEunde_pcBarunde_a), (a_CONSTANTunde_selfunde_a))) = (''Done'')))) \<and> ((((hce00c :: c)) = (a_STATEunde_PSexcl_varsunde_a))))))) \<or> ((((hce00c :: c)) = (a_STATEunde_PSexcl_varsunde_a)))))"(is "PROP ?ob'885")
proof -
ML_command {* writeln "*** TLAPS ENTER 885"; *}
show "PROP ?ob'885"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_8915cb.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_8915cb.znn.out
;; obligation #885
$hyp "v'62" a_STATEunde_Invunde_a
$hyp "v'63" hdb2fe
$hyp "v'64" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'72" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'81" (A. ((a_CONSTANTunde_xunde_a) (= (a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_xunde_a)
(a_CONSTANTunde_PSexcl_Cardinalityunde_a a_CONSTANTunde_xunde_a))))
$hyp "v'82" (= (TLA.fapply a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a)
"A")
$hyp "v'83" (TLA.bEx (TLA.subsetOf (TLA.SUBSET a_CONSTANTunde_Procunde_a) ((a_CONSTANTunde_Qunde_a) (/\ (TLA.in a_CONSTANTunde_punde_a
a_CONSTANTunde_Qunde_a) (TLA.bAll (TLA.setminus a_CONSTANTunde_Procunde_a
(TLA.set a_CONSTANTunde_punde_a)) ((a_CONSTANTunde_qunde_a) (\/ (-. (= (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_Qunde_a)))
(= a_CONSTANTunde_Qunde_a
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_qunde_a)))))))) ((a_CONSTANTunde_Punde_a) (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a a_CONSTANTunde_Punde_a))))
$hyp "v'84" (= a_h8b086a
(TLA.except a_STATEunde_pcBarunde_a a_CONSTANTunde_punde_a "Done"))
$goal (\/ (\/ (TLA.bEx a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_selfunde_a) (/\ (= (TLA.fapply a_STATEunde_pcBarunde_a a_CONSTANTunde_selfunde_a)
"A")
(TLA.bEx (TLA.subsetOf (TLA.SUBSET a_CONSTANTunde_Procunde_a) ((a_CONSTANTunde_Qunde_a) (/\ (TLA.in a_CONSTANTunde_selfunde_a
a_CONSTANTunde_Qunde_a) (TLA.bAll (TLA.setminus a_CONSTANTunde_Procunde_a
(TLA.set a_CONSTANTunde_selfunde_a)) ((a_CONSTANTunde_punde_a_1) (\/ (-. (= (a_CONSTANTunde_PSexcl_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a_1))
(a_CONSTANTunde_PSexcl_Cardinalityunde_a a_CONSTANTunde_Qunde_a)))
(= a_CONSTANTunde_Qunde_a
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a_1)))))))) ((a_CONSTANTunde_Punde_a) (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_selfunde_a a_CONSTANTunde_Punde_a))))
(= a_h8b086a
(TLA.except a_STATEunde_pcBarunde_a a_CONSTANTunde_selfunde_a "Done")))))
(/\ (TLA.bAll a_CONSTANTunde_PSexcl_ProcSetunde_a ((a_CONSTANTunde_selfunde_a) (= (TLA.fapply a_STATEunde_pcBarunde_a a_CONSTANTunde_selfunde_a)
"Done"))) (= hce00c a_STATEunde_PSexcl_varsunde_a))) (= hce00c
a_STATEunde_PSexcl_varsunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"(\\A a_CONSTANTunde_xunde_a:(a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_xunde_a)=a_CONSTANTunde_PSexcl_Cardinalityunde_a(a_CONSTANTunde_xunde_a)))" (is "\\A x : ?z_ho(x)")
 using v'81 by blast
 have z_Hi:"(a_h8b086a=except(a_STATEunde_pcBarunde_a, a_CONSTANTunde_punde_a, ''Done''))" (is "_=?z_hq")
 using v'84 by blast
 have z_Hh:"bEx(subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))), (\<lambda>a_CONSTANTunde_Punde_a. (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, a_CONSTANTunde_Punde_a))))" (is "?z_hh")
 using v'83 by blast
 have z_Hd:"(a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Procunde_a)" (is "?z_hd")
 using a_CONSTANTunde_punde_a_in by blast
 have z_Hg:"((a_STATEunde_pcBarunde_a[a_CONSTANTunde_punde_a])=''A'')" (is "?z_hbs=?z_hbt")
 using v'82 by blast
 assume z_Hj:"(~((bEx(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_selfunde_a. (((a_STATEunde_pcBarunde_a[a_CONSTANTunde_selfunde_a])=?z_hbt)&(bEx(subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_selfunde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_selfunde_a}), (\<lambda>a_CONSTANTunde_punde_a_1. ((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1])))))))), (\<lambda>a_CONSTANTunde_Punde_a. (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_selfunde_a, a_CONSTANTunde_Punde_a))))&(a_h8b086a=except(a_STATEunde_pcBarunde_a, a_CONSTANTunde_selfunde_a, ''Done''))))))|(bAll(a_CONSTANTunde_PSexcl_ProcSetunde_a, (\<lambda>a_CONSTANTunde_selfunde_a. ((a_STATEunde_pcBarunde_a[a_CONSTANTunde_selfunde_a])=''Done'')))&(hce00c=a_STATEunde_PSexcl_varsunde_a)))|(hce00c=a_STATEunde_PSexcl_varsunde_a)))" (is "~(?z_hbv|?z_hdd)")
 have z_Hdg_z_Hh: "(\\E x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x)))) == ?z_hh" (is "?z_hdg == _")
 by (unfold bEx_def)
 have z_Hdg: "?z_hdg" (is "\\E x : ?z_hdm(x)")
 by (unfold z_Hdg_z_Hh, fact z_Hh)
 have z_Hdn: "?z_hdm((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x)))))" (is "?z_hdp&?z_hdq")
 by (rule zenon_ex_choose_0 [of "?z_hdm", OF z_Hdg])
 have z_Hdp: "?z_hdp"
 by (rule zenon_and_0 [OF z_Hdn])
 have z_Hdq: "?z_hdq" (is "_=?z_hdr")
 by (rule zenon_and_1 [OF z_Hdn])
 have z_Hds: "((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x)))) \\in SUBSET(a_CONSTANTunde_Procunde_a))" (is "?z_hds")
 by (rule zenon_in_subsetof_0 [of "(CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))" "SUBSET(a_CONSTANTunde_Procunde_a)" "(\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))", OF z_Hdp])
 have z_Hdt: "((a_CONSTANTunde_punde_a \\in (CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x)))))&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))))|((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))))))" (is "?z_hdu&?z_hdv")
 by (rule zenon_in_subsetof_1 [of "(CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))" "SUBSET(a_CONSTANTunde_Procunde_a)" "(\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))", OF z_Hdp])
 have z_Hdu: "?z_hdu"
 by (rule zenon_and_0 [OF z_Hdt])
 have z_Hdv: "?z_hdv"
 by (rule zenon_and_1 [OF z_Hdt])
 have z_Heb_z_Hdv: "(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))~=a_CONSTANTunde_Cardinalityunde_a((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))))|((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))=(a_VARIABLEunde_resultunde_a[x]))))) == ?z_hdv" (is "?z_heb == _")
 by (unfold bAll_def)
 have z_Heb: "?z_heb" (is "\\A x : ?z_hej(x)")
 by (unfold z_Heb_z_Hdv, fact z_Hdv)
 have z_Hek: "(~?z_hbv)" (is "~(?z_hbw|?z_hcy)")
 by (rule zenon_notor_0 [OF z_Hj])
 have z_Hel: "(~?z_hbw)"
 by (rule zenon_notor_0 [OF z_Hek])
 have z_Hem_z_Hel: "(~(\\E x:((x \\in a_CONSTANTunde_Procunde_a)&(((a_STATEunde_pcBarunde_a[x])=?z_hbt)&(bEx(subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((x \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {x}), (\<lambda>a_CONSTANTunde_punde_a_1. ((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1])))))))), (\<lambda>a_CONSTANTunde_Punde_a. (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, x, a_CONSTANTunde_Punde_a))))&(a_h8b086a=except(a_STATEunde_pcBarunde_a, x, ''Done''))))))) == (~?z_hbw)" (is "?z_hem == ?z_hel")
 by (unfold bEx_def)
 have z_Hem: "?z_hem" (is "~(\\E x : ?z_hfh(x))")
 by (unfold z_Hem_z_Hel, fact z_Hel)
 have z_Hfi: "~?z_hfh(a_CONSTANTunde_punde_a)" (is "~(_&?z_hfj)")
 by (rule zenon_notex_0 [of "?z_hfh" "a_CONSTANTunde_punde_a", OF z_Hem])
 show FALSE
 proof (rule zenon_notand [OF z_Hfi])
  assume z_Hfk:"(~?z_hd)"
  show FALSE
  by (rule notE [OF z_Hfk z_Hd])
 next
  assume z_Hfl:"(~?z_hfj)" (is "~(?z_hg&?z_hfm)")
  show FALSE
  proof (rule zenon_notand [OF z_Hfl])
   assume z_Hfn:"(?z_hbs~=?z_hbt)"
   show FALSE
   by (rule notE [OF z_Hfn z_Hg])
  next
   assume z_Hfo:"(~?z_hfm)" (is "~(?z_hfp&?z_hi)")
   show FALSE
   proof (rule zenon_notand [OF z_Hfo])
    assume z_Hfq:"(~?z_hfp)"
    have z_Hfr_z_Hfq: "(~(\\E x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_punde_a_1. ((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))) == (~?z_hfp)" (is "?z_hfr == ?z_hfq")
    by (unfold bEx_def)
    have z_Hfr: "?z_hfr" (is "~(\\E x : ?z_hfz(x))")
    by (unfold z_Hfr_z_Hfq, fact z_Hfq)
    have z_Hga: "~?z_hfz((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x)))))" (is "~(?z_hgb&_)")
    by (rule zenon_notex_0 [of "?z_hfz" "(CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))", OF z_Hfr])
    show FALSE
    proof (rule zenon_notand [OF z_Hga])
     assume z_Hgc:"(~?z_hgb)"
     show FALSE
     proof (rule zenon_notin_subsetof [of "(CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))" "SUBSET(a_CONSTANTunde_Procunde_a)" "(\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_punde_a_1. ((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1])))))))", OF z_Hgc])
      assume z_Hgd:"(~?z_hds)"
      show FALSE
      by (rule notE [OF z_Hgd z_Hds])
     next
      assume z_Hge:"(~(?z_hdu&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_punde_a_1. ((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))))|((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_punde_a_1])))))))" (is "~(_&?z_hgg)")
      show FALSE
      proof (rule zenon_notand [OF z_Hge])
       assume z_Hgm:"(~?z_hdu)"
       show FALSE
       by (rule notE [OF z_Hgm z_Hdu])
      next
       assume z_Hgn:"(~?z_hgg)"
       have z_Hgo_z_Hgn: "(~(\\A x:((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))))|((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))=(a_VARIABLEunde_resultunde_a[x])))))) == (~?z_hgg)" (is "?z_hgo == ?z_hgn")
       by (unfold bAll_def)
       have z_Hgo: "?z_hgo" (is "~(\\A x : ?z_hgu(x))")
       by (unfold z_Hgo_z_Hgn, fact z_Hgn)
       have z_Hgv: "(\\E x:(~((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))))|((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))=(a_VARIABLEunde_resultunde_a[x]))))))" (is "\\E x : ?z_hgx(x)")
       by (rule zenon_notallex_0 [of "?z_hgu", OF z_Hgo])
       have z_Hgy: "?z_hgx((CHOOSE x:(~((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))))|((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))=(a_VARIABLEunde_resultunde_a[x])))))))" (is "~(?z_hha=>?z_hhb)")
       by (rule zenon_ex_choose_0 [of "?z_hgx", OF z_Hgv])
       have z_Hha: "?z_hha"
       by (rule zenon_notimply_0 [OF z_Hgy])
       have z_Hhc: "(~?z_hhb)" (is "~(?z_hhd|?z_hhe)")
       by (rule zenon_notimply_1 [OF z_Hgy])
       have z_Hhf: "(~?z_hhd)" (is "~~?z_hhg")
       by (rule zenon_notor_0 [OF z_Hhc])
       have z_Hhh: "((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))~=(a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))~=a_CONSTANTunde_PSexcl_Cardinalityunde_a((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))))|((CHOOSE x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))=(a_VARIABLEunde_resultunde_a[x]))))))]))" (is "?z_hdo~=?z_hhi")
       by (rule zenon_notor_1 [OF z_Hhc])
       have z_Hhg: "?z_hhg" (is "?z_hhj=?z_hgk")
       by (rule zenon_notnot_0 [OF z_Hhf])
       have z_Hhk: "?z_hej((CHOOSE x:(~((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))~=?z_hgk)|(?z_hdo=(a_VARIABLEunde_resultunde_a[x])))))))" (is "_=>?z_hhl")
       by (rule zenon_all_0 [of "?z_hej" "(CHOOSE x:(~((x \\in (a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}))=>((a_CONSTANTunde_PSexcl_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))~=?z_hgk)|(?z_hdo=(a_VARIABLEunde_resultunde_a[x]))))))", OF z_Heb])
       show FALSE
       proof (rule zenon_imply [OF z_Hhk])
        assume z_Hhm:"(~?z_hha)"
        show FALSE
        by (rule notE [OF z_Hhm z_Hha])
       next
        assume z_Hhl:"?z_hhl" (is "?z_hhn|_")
        show FALSE
        proof (rule zenon_or [OF z_Hhl])
         assume z_Hhn:"?z_hhn" (is "?z_hho~=?z_hdz")
         have z_Hhp: "?z_ho(?z_hhi)"
         by (rule zenon_all_0 [of "?z_ho" "?z_hhi", OF z_Hf])
         have z_Hhq: "(?z_hhj~=?z_hdz)"
         by (rule subst [where P="(\<lambda>zenon_Vrg. (zenon_Vrg~=?z_hdz))", OF z_Hhp z_Hhn])
         have z_Hhu: "?z_ho(?z_hdo)"
         by (rule zenon_all_0 [of "?z_ho" "?z_hdo", OF z_Hf])
         have z_Hhd: "?z_hhd"
         by (rule subst [where P="(\<lambda>zenon_Vsg. (?z_hhj~=zenon_Vsg))", OF z_Hhu z_Hhq])
         show FALSE
         by (rule notE [OF z_Hhd z_Hhg])
        next
         assume z_Hhe:"?z_hhe"
         show FALSE
         by (rule notE [OF z_Hhh z_Hhe])
        qed
       qed
      qed
     qed
    next
     assume z_Hhy:"(a_VARIABLEunde_resultunde_hash_primea~=?z_hdr)"
     show FALSE
     by (rule notE [OF z_Hhy z_Hdq])
    qed
   next
    assume z_Hhz:"(a_h8b086a~=?z_hq)"
    show FALSE
    by (rule notE [OF z_Hhz z_Hi])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 885"; *} qed
lemma ob'851:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
assumes v'48: "((((((((((a_VARIABLEunde_A1unde_a) \<in> ([(Nat) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_resultunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_pcunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ({(''a''), (''b''), (''Done'')})]))) & (((a_VARIABLEunde_knownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (a_CONSTANTunde_Procunde_a)))]))) & (((a_VARIABLEunde_notKnownunde_a) \<in> ([(a_CONSTANTunde_Procunde_a) \<rightarrow> ((SUBSET (Nat)))]))) & (\<forall> a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a) : (((((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b''))) \<Rightarrow> (((fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) \<noteq> ({}))))))) \<and> (a_STATEunde_InvBunde_a))) \<and> (a_STATEunde_InvCunde_a))) \<and> (\<forall> a_CONSTANTunde_iunde_a \<in> (a_CONSTANTunde_Procunde_a) : (\<forall> a_CONSTANTunde_junde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((((((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_iunde_a))) \<noteq> ({}))) \<and> (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_junde_a))) \<noteq> ({}))))) & ((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_iunde_a)))))) = ((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_junde_a))))))))) \<Rightarrow> (((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_iunde_a))) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_junde_a)))))))))))"
assumes v'49: "(a_ACTIONunde_Nextunde_a)"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'63: "(\<exists> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A1unde_hash_primea :: c)) = ([(a_VARIABLEunde_A1unde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"
assumes v'64: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b'')))"
assumes v'65: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''a'')])))"
assumes v'66: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'67: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = (a_VARIABLEunde_knownunde_a)))"
assumes v'68: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = (a_VARIABLEunde_notKnownunde_a)))"
assumes v'73: "(\<exists> a_CONSTANTunde_iunde_a \<in> (fapply ((a_VARIABLEunde_notKnownunde_a), (a_CONSTANTunde_punde_a))) : ((((a_VARIABLEunde_A1unde_hash_primea :: c)) = ([(a_VARIABLEunde_A1unde_a) EXCEPT ![(a_CONSTANTunde_iunde_a)] = (fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a)))]))))"
assumes v'74: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''b'')))"
assumes v'75: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''a'')])))"
assumes v'76: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = (a_VARIABLEunde_resultunde_a)))"
assumes v'77: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = (a_VARIABLEunde_knownunde_a)))"
assumes v'78: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = (a_VARIABLEunde_notKnownunde_a)))"
shows "(\<forall> a_CONSTANTunde_iunde_a \<in> (a_CONSTANTunde_Procunde_a) : (\<forall> a_CONSTANTunde_junde_a \<in> (a_CONSTANTunde_Procunde_a) : ((((((((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_iunde_a))) \<noteq> ({}))) \<and> (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_junde_a))) \<noteq> ({}))))) & ((((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_iunde_a)))))) = ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_junde_a))))))))) \<Rightarrow> (((fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_iunde_a))) = (fapply (((a_VARIABLEunde_resultunde_hash_primea :: c)), (a_CONSTANTunde_junde_a)))))))))"(is "PROP ?ob'851")
proof -
ML_command {* writeln "*** TLAPS ENTER 851"; *}
show "PROP ?ob'851"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_2f8b19.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_2f8b19.znn.out
;; obligation #851
$hyp "v'48" (/\ (/\ (/\ (/\ (TLA.in a_VARIABLEunde_A1unde_a
(TLA.FuncSet arith.N (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_resultunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_pcunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.set "a" "b" "Done")))
(TLA.in a_VARIABLEunde_knownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET a_CONSTANTunde_Procunde_a)))
(TLA.in a_VARIABLEunde_notKnownunde_a
(TLA.FuncSet a_CONSTANTunde_Procunde_a (TLA.SUBSET arith.N)))
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_punde_a) (=> (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b") (-. (= (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a)
TLA.emptyset)))))) a_STATEunde_InvBunde_a) a_STATEunde_InvCunde_a)
(TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_iunde_a) (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_junde_a) (=> (/\ (/\ (-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_iunde_a)
TLA.emptyset))
(-. (= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_junde_a)
TLA.emptyset)))
(= (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_iunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_junde_a))))
(= (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_iunde_a)
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_junde_a))))))))
$hyp "v'49" a_ACTIONunde_Nextunde_a
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'63" (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (= a_VARIABLEunde_A1unde_hash_primea
(TLA.except a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
$hyp "v'64" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
$hyp "v'65" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "a"))
$hyp "v'66" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'67" (= a_VARIABLEunde_knownunde_hash_primea
a_VARIABLEunde_knownunde_a)
$hyp "v'68" (= a_VARIABLEunde_notKnownunde_hash_primea
a_VARIABLEunde_notKnownunde_a)
$hyp "v'73" (TLA.bEx (TLA.fapply a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a) ((a_CONSTANTunde_iunde_a) (= a_VARIABLEunde_A1unde_hash_primea
(TLA.except a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)))))
$hyp "v'74" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"b")
$hyp "v'75" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "a"))
$hyp "v'76" (= a_VARIABLEunde_resultunde_hash_primea
a_VARIABLEunde_resultunde_a)
$hyp "v'77" (= a_VARIABLEunde_knownunde_hash_primea
a_VARIABLEunde_knownunde_a)
$hyp "v'78" (= a_VARIABLEunde_notKnownunde_hash_primea
a_VARIABLEunde_notKnownunde_a)
$goal (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_iunde_a) (TLA.bAll a_CONSTANTunde_Procunde_a ((a_CONSTANTunde_junde_a) (=> (/\ (/\ (-. (= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_iunde_a)
TLA.emptyset))
(-. (= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_junde_a)
TLA.emptyset)))
(= (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_iunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_junde_a))))
(= (TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_iunde_a)
(TLA.fapply a_VARIABLEunde_resultunde_hash_primea a_CONSTANTunde_junde_a)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((((a_VARIABLEunde_A1unde_a \\in FuncSet(Nat, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_resultunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_pcunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, {''a'', ''b'', ''Done''}))&((a_VARIABLEunde_knownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(a_CONSTANTunde_Procunde_a)))&((a_VARIABLEunde_notKnownunde_a \\in FuncSet(a_CONSTANTunde_Procunde_a, SUBSET(Nat)))&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_punde_a. (((a_VARIABLEunde_pcunde_a[a_CONSTANTunde_punde_a])=''b'')=>((a_VARIABLEunde_notKnownunde_a[a_CONSTANTunde_punde_a])~={})))))))))&a_STATEunde_InvBunde_a)&a_STATEunde_InvCunde_a)&bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_iunde_a. bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_iunde_a])~={})&((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_iunde_a]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_iunde_a])=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_junde_a]))))))))" (is "?z_hk&?z_hbx")
 using v'48 by blast
 have z_Hg:"(a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a)"
 using v'76 by blast
 have zenon_L1_: "((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])~=(a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hcp ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hcp:"?z_hcp" (is "?z_hcq~=?z_hdu")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule zenon_noteq [of "?z_hdu"])
   have z_Hdv: "(?z_hdu~=?z_hdu)"
   by (rule subst [where P="(\<lambda>zenon_Vxvf. ((zenon_Vxvf[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])~=?z_hdu))", OF z_Hg], fact z_Hcp)
   thus "(?z_hdu~=?z_hdu)" .
  qed
 qed
 have zenon_L2_: "((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])~={}) ==> ((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])={}) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hea ==> ?z_heb ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hea:"?z_hea" (is "?z_hcq~=_")
  assume z_Heb:"?z_heb" (is "?z_hdu=_")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule notE [OF z_Hea])
   have z_Hec: "(?z_hdu=?z_hcq)"
   proof (rule zenon_nnpp [of "(?z_hdu=?z_hcq)"])
    assume z_Hed:"(?z_hdu~=?z_hcq)"
    show FALSE
    proof (rule zenon_em [of "(?z_hcq=?z_hcq)"])
     assume z_Hee:"(?z_hcq=?z_hcq)"
     show FALSE
     proof (rule notE [OF z_Hed])
      have z_Hef: "(?z_hcq=?z_hdu)"
      proof (rule zenon_nnpp [of "(?z_hcq=?z_hdu)"])
       assume z_Hcp:"(?z_hcq~=?z_hdu)"
       show FALSE
       by (rule zenon_L1_ [OF z_Hcp z_Hg])
      qed
      have z_Hec: "(?z_hdu=?z_hcq)"
      by (rule subst [where P="(\<lambda>zenon_Vyvf. (zenon_Vyvf=?z_hcq))", OF z_Hef], fact z_Hee)
      thus "(?z_hdu=?z_hcq)" .
     qed
    next
     assume z_Hej:"(?z_hcq~=?z_hcq)"
     show FALSE
     by (rule zenon_noteq [OF z_Hej])
    qed
   qed
   have z_Hek: "(?z_hcq={})"
   by (rule subst [where P="(\<lambda>zenon_Vzvf. (zenon_Vzvf={}))", OF z_Hec], fact z_Heb)
   thus "(?z_hcq={})" .
  qed
 qed
 have zenon_L3_: "((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~=(a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_heo ==> ?z_hg ==> FALSE")
 proof -
  assume z_Heo:"?z_heo" (is "?z_hda~=?z_hep")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule zenon_noteq [of "?z_hep"])
   have z_Heq: "(?z_hep~=?z_hep)"
   by (rule subst [where P="(\<lambda>zenon_Vawf. ((zenon_Vawf[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~=?z_hep))", OF z_Hg], fact z_Heo)
   thus "(?z_hep~=?z_hep)" .
  qed
 qed
 have zenon_L4_: "((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={}) ==> ((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])={}) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hcz ==> ?z_hev ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hcz:"?z_hcz" (is "?z_hda~=_")
  assume z_Hev:"?z_hev" (is "?z_hep=_")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule notE [OF z_Hcz])
   have z_Hew: "(?z_hep=?z_hda)"
   proof (rule zenon_nnpp [of "(?z_hep=?z_hda)"])
    assume z_Hex:"(?z_hep~=?z_hda)"
    show FALSE
    proof (rule zenon_em [of "(?z_hda=?z_hda)"])
     assume z_Hey:"(?z_hda=?z_hda)"
     show FALSE
     proof (rule notE [OF z_Hex])
      have z_Hez: "(?z_hda=?z_hep)"
      proof (rule zenon_nnpp [of "(?z_hda=?z_hep)"])
       assume z_Heo:"(?z_hda~=?z_hep)"
       show FALSE
       by (rule zenon_L3_ [OF z_Heo z_Hg])
      qed
      have z_Hew: "(?z_hep=?z_hda)"
      by (rule subst [where P="(\<lambda>zenon_Vbwf. (zenon_Vbwf=?z_hda))", OF z_Hez], fact z_Hey)
      thus "(?z_hep=?z_hda)" .
     qed
    next
     assume z_Hfd:"(?z_hda~=?z_hda)"
     show FALSE
     by (rule zenon_noteq [OF z_Hfd])
    qed
   qed
   have z_Hfe: "(?z_hda={})"
   by (rule subst [where P="(\<lambda>zenon_Vzvf. (zenon_Vzvf={}))", OF z_Hew], fact z_Hev)
   thus "(?z_hda={})" .
  qed
 qed
 have zenon_L5_: "((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~=(a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hex ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hex:"?z_hex" (is "?z_hep~=?z_hda")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule zenon_noteq [of "?z_hda"])
   have z_Hff: "(a_VARIABLEunde_resultunde_a=a_VARIABLEunde_resultunde_hash_primea)"
   by (rule sym [OF z_Hg])
   have z_Hfd: "(?z_hda~=?z_hda)"
   by (rule subst [where P="(\<lambda>zenon_Vdwf. ((zenon_Vdwf[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~=?z_hda))", OF z_Hff], fact z_Hex)
   thus "(?z_hda~=?z_hda)" .
  qed
 qed
 have zenon_L6_: "(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))~=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> FALSE" (is "?z_hfk ==> ?z_hg ==> FALSE")
 proof -
  assume z_Hfk:"?z_hfk" (is "?z_hfl~=?z_hfm")
  assume z_Hg:"?z_hg"
  show FALSE
  proof (rule zenon_noteq [of "?z_hfm"])
   have z_Hef: "((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])=(a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))" (is "?z_hcq=?z_hdu")
   proof (rule zenon_nnpp [of "(?z_hcq=?z_hdu)"])
    assume z_Hcp:"(?z_hcq~=?z_hdu)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hcp z_Hg])
   qed
   have z_Hfn: "(?z_hfm~=?z_hfm)"
   by (rule subst [where P="(\<lambda>zenon_Vewf. (a_CONSTANTunde_Cardinalityunde_a(zenon_Vewf)~=?z_hfm))", OF z_Hef], fact z_Hfk)
   thus "(?z_hfm~=?z_hfm)" .
  qed
 qed
 have zenon_L7_: "(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> (a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))~=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))) ==> FALSE" (is "?z_hfs ==> ?z_hg ==> ?z_hft ==> FALSE")
 proof -
  assume z_Hfs:"?z_hfs" (is "?z_hds=?z_hfl")
  assume z_Hg:"?z_hg"
  assume z_Hft:"?z_hft" (is "?z_hfm~=?z_hfu")
  show FALSE
  proof (rule zenon_em [of "(?z_hfu=?z_hfu)"])
   assume z_Hfv:"(?z_hfu=?z_hfu)"
   show FALSE
   proof (rule notE [OF z_Hft])
    have z_Hfw: "(?z_hfu=?z_hfm)"
    proof (rule zenon_nnpp [of "(?z_hfu=?z_hfm)"])
     assume z_Hfx:"(?z_hfu~=?z_hfm)"
     show FALSE
     proof (rule notE [OF z_Hfx])
      have z_Hfy: "(?z_hds=?z_hfu)"
      proof (rule zenon_nnpp [of "(?z_hds=?z_hfu)"])
       assume z_Hfz:"(?z_hds~=?z_hfu)"
       show FALSE
       proof (rule zenon_em [of "(?z_hfu=?z_hfu)"])
        assume z_Hfv:"(?z_hfu=?z_hfu)"
        show FALSE
        proof (rule notE [OF z_Hfz])
         have z_Hga: "(?z_hfu=?z_hds)"
         proof (rule zenon_nnpp [of "(?z_hfu=?z_hds)"])
          assume z_Hgb:"(?z_hfu~=?z_hds)"
          show FALSE
          proof (rule zenon_noteq [of "?z_hds"])
           have z_Hew: "((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))" (is "?z_hep=?z_hda")
           proof (rule zenon_nnpp [of "(?z_hep=?z_hda)"])
            assume z_Hex:"(?z_hep~=?z_hda)"
            show FALSE
            by (rule zenon_L5_ [OF z_Hex z_Hg])
           qed
           have z_Hgc: "(?z_hds~=?z_hds)"
           by (rule subst [where P="(\<lambda>zenon_Vfwf. (a_CONSTANTunde_Cardinalityunde_a(zenon_Vfwf)~=?z_hds))", OF z_Hew], fact z_Hgb)
           thus "(?z_hds~=?z_hds)" .
          qed
         qed
         have z_Hfy: "(?z_hds=?z_hfu)"
         by (rule subst [where P="(\<lambda>zenon_Vgwf. (zenon_Vgwf=?z_hfu))", OF z_Hga], fact z_Hfv)
         thus "(?z_hds=?z_hfu)" .
        qed
       next
        assume z_Hgk:"(?z_hfu~=?z_hfu)"
        show FALSE
        by (rule zenon_noteq [OF z_Hgk])
       qed
      qed
      have z_Hgl: "(?z_hfl=?z_hfm)"
      proof (rule zenon_nnpp [of "(?z_hfl=?z_hfm)"])
       assume z_Hfk:"(?z_hfl~=?z_hfm)"
       show FALSE
       by (rule zenon_L6_ [OF z_Hfk z_Hg])
      qed
      have z_Hgm: "(?z_hfu=?z_hfl)"
      by (rule subst [where P="(\<lambda>zenon_Vhwf. (zenon_Vhwf=?z_hfl))", OF z_Hfy], fact z_Hfs)
      have z_Hfw: "(?z_hfu=?z_hfm)"
      by (rule subst [where P="(\<lambda>zenon_Viwf. (?z_hfu=zenon_Viwf))", OF z_Hgl], fact z_Hgm)
      thus "(?z_hfu=?z_hfm)" .
     qed
    qed
    have z_Hgt: "(?z_hfm=?z_hfu)"
    by (rule subst [where P="(\<lambda>zenon_Vgwf. (zenon_Vgwf=?z_hfu))", OF z_Hfw], fact z_Hfv)
    thus "(?z_hfm=?z_hfu)" .
   qed
  next
   assume z_Hgk:"(?z_hfu~=?z_hfu)"
   show FALSE
   by (rule zenon_noteq [OF z_Hgk])
  qed
 qed
 have zenon_L8_: "((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])=(a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])) ==> (a_VARIABLEunde_resultunde_hash_primea=a_VARIABLEunde_resultunde_a) ==> ((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~=(a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])) ==> FALSE" (is "?z_hgu ==> ?z_hg ==> ?z_hgv ==> FALSE")
 proof -
  assume z_Hgu:"?z_hgu" (is "?z_hdu=?z_hep")
  assume z_Hg:"?z_hg"
  assume z_Hgv:"?z_hgv" (is "?z_hda~=?z_hcq")
  show FALSE
  proof (rule zenon_em [of "(?z_hcq=?z_hcq)"])
   assume z_Hee:"(?z_hcq=?z_hcq)"
   show FALSE
   proof (rule notE [OF z_Hgv])
    have z_Hgw: "(?z_hcq=?z_hda)"
    proof (rule zenon_nnpp [of "(?z_hcq=?z_hda)"])
     assume z_Hgx:"(?z_hcq~=?z_hda)"
     show FALSE
     proof (rule notE [OF z_Hgx])
      have z_Hec: "(?z_hdu=?z_hcq)"
      proof (rule zenon_nnpp [of "(?z_hdu=?z_hcq)"])
       assume z_Hed:"(?z_hdu~=?z_hcq)"
       show FALSE
       proof (rule zenon_em [of "(?z_hcq=?z_hcq)"])
        assume z_Hee:"(?z_hcq=?z_hcq)"
        show FALSE
        proof (rule notE [OF z_Hed])
         have z_Hef: "(?z_hcq=?z_hdu)"
         proof (rule zenon_nnpp [of "(?z_hcq=?z_hdu)"])
          assume z_Hcp:"(?z_hcq~=?z_hdu)"
          show FALSE
          by (rule zenon_L1_ [OF z_Hcp z_Hg])
         qed
         have z_Hec: "(?z_hdu=?z_hcq)"
         by (rule subst [where P="(\<lambda>zenon_Vyvf. (zenon_Vyvf=?z_hcq))", OF z_Hef], fact z_Hee)
         thus "(?z_hdu=?z_hcq)" .
        qed
       next
        assume z_Hej:"(?z_hcq~=?z_hcq)"
        show FALSE
        by (rule zenon_noteq [OF z_Hej])
       qed
      qed
      have z_Hew: "(?z_hep=?z_hda)"
      proof (rule zenon_nnpp [of "(?z_hep=?z_hda)"])
       assume z_Hex:"(?z_hep~=?z_hda)"
       show FALSE
       by (rule zenon_L5_ [OF z_Hex z_Hg])
      qed
      have z_Hgy: "(?z_hcq=?z_hep)"
      by (rule subst [where P="(\<lambda>zenon_Vlwf. (zenon_Vlwf=?z_hep))", OF z_Hec], fact z_Hgu)
      have z_Hgw: "(?z_hcq=?z_hda)"
      by (rule subst [where P="(\<lambda>zenon_Vmwf. (?z_hcq=zenon_Vmwf))", OF z_Hew], fact z_Hgy)
      thus "(?z_hcq=?z_hda)" .
     qed
    qed
    have z_Hhf: "(?z_hda=?z_hcq)"
    by (rule subst [where P="(\<lambda>zenon_Vyvf. (zenon_Vyvf=?z_hcq))", OF z_Hgw], fact z_Hee)
    thus "(?z_hda=?z_hcq)" .
   qed
  next
   assume z_Hej:"(?z_hcq~=?z_hcq)"
   show FALSE
   by (rule zenon_noteq [OF z_Hej])
  qed
 qed
 assume z_Hj:"(~bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_iunde_a. bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_iunde_a])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_iunde_a]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_iunde_a])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))" (is "~?z_hhg")
 have z_Hbx: "?z_hbx"
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hhs_z_Hbx: "(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_a[x])~={})&((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_a[x])=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_junde_a]))))))) == ?z_hbx" (is "?z_hhs == _")
 by (unfold bAll_def)
 have z_Hhs: "?z_hhs" (is "\\A x : ?z_hie(x)")
 by (unfold z_Hhs_z_Hbx, fact z_Hbx)
 have z_Hif_z_Hj: "(~(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])))))))) == (~?z_hhg)" (is "?z_hif == ?z_hj")
 by (unfold bAll_def)
 have z_Hif: "?z_hif" (is "~(\\A x : ?z_hih(x))")
 by (unfold z_Hif_z_Hj, fact z_Hj)
 have z_Hii: "(\\E x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))" (is "\\E x : ?z_hij(x)")
 by (rule zenon_notallex_0 [of "?z_hih", OF z_Hif])
 have z_Hik: "?z_hij((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])))))))))" (is "~(?z_hil=>?z_him)")
 by (rule zenon_ex_choose_0 [of "?z_hij", OF z_Hii])
 have z_Hil: "?z_hil"
 by (rule zenon_notimply_0 [OF z_Hik])
 have z_Hin: "(~?z_him)"
 by (rule zenon_notimply_1 [OF z_Hik])
 have z_Hio_z_Hin: "(~(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x])))))) == (~?z_him)" (is "?z_hio == ?z_hin")
 by (unfold bAll_def)
 have z_Hio: "?z_hio" (is "~(\\A x : ?z_hiq(x))")
 by (unfold z_Hio_z_Hin, fact z_Hin)
 have z_Hir: "(\\E x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))" (is "\\E x : ?z_his(x)")
 by (rule zenon_notallex_0 [of "?z_hiq", OF z_Hio])
 have z_Hit: "?z_his((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x])))))))" (is "~(?z_hiu=>?z_hiv)")
 by (rule zenon_ex_choose_0 [of "?z_his", OF z_Hir])
 have z_Hiu: "?z_hiu"
 by (rule zenon_notimply_0 [OF z_Hit])
 have z_Hiw: "(~?z_hiv)" (is "~(?z_hix=>?z_hhf)")
 by (rule zenon_notimply_1 [OF z_Hit])
 have z_Hix: "?z_hix" (is "?z_hiy&?z_hfs")
 by (rule zenon_notimply_0 [OF z_Hiw])
 have z_Hgv: "((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~=(a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])~={})&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>((a_VARIABLEunde_resultunde_hash_primea[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))" (is "?z_hda~=?z_hcq")
 by (rule zenon_notimply_1 [OF z_Hiw])
 have z_Hiy: "?z_hiy" (is "?z_hcz&?z_hea")
 by (rule zenon_and_0 [OF z_Hix])
 have z_Hfs: "?z_hfs" (is "?z_hds=?z_hfl")
 by (rule zenon_and_1 [OF z_Hix])
 have z_Hcz: "?z_hcz"
 by (rule zenon_and_0 [OF z_Hiy])
 have z_Hea: "?z_hea"
 by (rule zenon_and_1 [OF z_Hiy])
 have z_Hiz: "?z_hie((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((?z_hcz&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(?z_hds=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>(?z_hda=(a_VARIABLEunde_resultunde_hash_primea[x])))))))" (is "_=>?z_hja")
 by (rule zenon_all_0 [of "?z_hie" "(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((?z_hcz&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(?z_hds=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>(?z_hda=(a_VARIABLEunde_resultunde_hash_primea[x]))))))", OF z_Hhs])
 show FALSE
 proof (rule zenon_imply [OF z_Hiz])
  assume z_Hjb:"(~?z_hiu)"
  show FALSE
  by (rule notE [OF z_Hjb z_Hiu])
 next
  assume z_Hja:"?z_hja"
  have z_Hjc_z_Hja: "(\\A x:((x \\in a_CONSTANTunde_Procunde_a)=>(((((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((?z_hcz&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(?z_hds=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>(?z_hda=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])~={})&((a_VARIABLEunde_resultunde_a[x])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((?z_hcz&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(?z_hds=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>(?z_hda=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[x]))))=>((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((?z_hcz&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(?z_hds=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>(?z_hda=(a_VARIABLEunde_resultunde_hash_primea[x]))))))])=(a_VARIABLEunde_resultunde_a[x]))))) == ?z_hja" (is "?z_hjc == _")
  by (unfold bAll_def)
  have z_Hjc: "?z_hjc" (is "\\A x : ?z_hjk(x)")
  by (unfold z_Hjc_z_Hja, fact z_Hja)
  have z_Hjl: "?z_hjk((CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])))))))))" (is "_=>?z_hjm")
  by (rule zenon_all_0 [of "?z_hjk" "(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))", OF z_Hjc])
  show FALSE
  proof (rule zenon_imply [OF z_Hjl])
   assume z_Hjn:"(~?z_hil)"
   show FALSE
   by (rule notE [OF z_Hjn z_Hil])
  next
   assume z_Hjm:"?z_hjm" (is "?z_hjo=>?z_hgu")
   show FALSE
   proof (rule zenon_imply [OF z_Hjm])
    assume z_Hjp:"(~?z_hjo)" (is "~(?z_hjq&?z_hgt)")
    show FALSE
    proof (rule zenon_notand [OF z_Hjp])
     assume z_Hjr:"(~?z_hjq)" (is "~(?z_hjh&?z_hjs)")
     show FALSE
     proof (rule zenon_notand [OF z_Hjr])
      assume z_Hjt:"(~?z_hjh)" (is "~~?z_heb")
      have z_Heb: "?z_heb" (is "?z_hdu=_")
      by (rule zenon_notnot_0 [OF z_Hjt])
      show FALSE
      by (rule zenon_L2_ [OF z_Hea z_Heb z_Hg])
     next
      assume z_Hju:"(~?z_hjs)" (is "~~?z_hev")
      have z_Hev: "?z_hev" (is "?z_hep=_")
      by (rule zenon_notnot_0 [OF z_Hju])
      show FALSE
      by (rule zenon_L4_ [OF z_Hcz z_Hev z_Hg])
     qed
    next
     assume z_Hft:"(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>(((?z_hcz&((a_VARIABLEunde_resultunde_hash_primea[x])~={}))&(?z_hds=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))))=>(?z_hda=(a_VARIABLEunde_resultunde_hash_primea[x]))))))]))~=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[(CHOOSE x:(~((x \\in a_CONSTANTunde_Procunde_a)=>bAll(a_CONSTANTunde_Procunde_a, (\<lambda>a_CONSTANTunde_junde_a. (((((a_VARIABLEunde_resultunde_hash_primea[x])~={})&((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a])~={}))&(a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[x]))=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))=>((a_VARIABLEunde_resultunde_hash_primea[x])=(a_VARIABLEunde_resultunde_hash_primea[a_CONSTANTunde_junde_a]))))))))])))" (is "?z_hfm~=?z_hfu")
     show FALSE
     by (rule zenon_L7_ [OF z_Hfs z_Hg z_Hft])
    qed
   next
    assume z_Hgu:"?z_hgu" (is "?z_hdu=?z_hep")
    show FALSE
    by (rule zenon_L8_ [OF z_Hgu z_Hg z_Hgv])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 851"; *} qed
lemma ob'898:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Procunde_a
fixes a_VARIABLEunde_A1unde_a a_VARIABLEunde_A1unde_a'
fixes a_VARIABLEunde_resultunde_a a_VARIABLEunde_resultunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
fixes a_VARIABLEunde_knownunde_a a_VARIABLEunde_knownunde_a'
fixes a_VARIABLEunde_notKnownunde_a a_VARIABLEunde_notKnownunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition CONSTANT_ProcSet_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_a_ suppressed *)
(* usable definition ACTION_b_ suppressed *)
(* usable definition ACTION_Pr_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition STATE_snapshot_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
(* usable definition STATE_Done_ suppressed *)
(* usable definition STATE_GFXCorrect_ suppressed *)
(* usable definition CONSTANT_NotAProc_ suppressed *)
(* usable definition STATE_ReadyToWrite_ suppressed *)
(* usable definition STATE_WriterAssignment_ suppressed *)
(* usable definition STATE_PV_ suppressed *)
(* usable definition STATE_PA1_ suppressed *)
(* usable definition STATE_InvB_ suppressed *)
(* usable definition STATE_InvC_ suppressed *)
(* usable definition STATE_Inv_ suppressed *)
(* usable definition CONSTANT_Test_ suppressed *)
(* usable definition STATE_pcBar_ suppressed *)
(* usable definition CONSTANT_PS!IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_PS!Cardinality_ suppressed *)
(* usable definition STATE_PS!vars_ suppressed *)
(* usable definition CONSTANT_PS!ProcSet_ suppressed *)
(* usable definition STATE_PS!Init_ suppressed *)
(* usable definition ACTION_PS!A_ suppressed *)
(* usable definition ACTION_PS!Pr_ suppressed *)
(* usable definition ACTION_PS!Next_ suppressed *)
(* usable definition TEMPORAL_PS!Spec_ suppressed *)
(* usable definition STATE_PS!Termination_ suppressed *)
(* usable definition STATE_PS!TypeOK_ suppressed *)
(* usable definition STATE_PS!Done_ suppressed *)
(* usable definition STATE_PS!GFXCorrect_ suppressed *)
assumes v'65: "(a_STATEunde_Invunde_a)"
assumes v'66: "((hdb2fe :: c))"
assumes v'67: "(((a_ACTIONunde_Nextunde_a) \<or> ((((h6fbaa :: c)) = (a_STATEunde_varsunde_a)))))"
fixes a_CONSTANTunde_punde_a
assumes a_CONSTANTunde_punde_a_in : "(a_CONSTANTunde_punde_a \<in> (a_CONSTANTunde_Procunde_a))"
assumes v'75: "(((fapply ((a_VARIABLEunde_pcunde_a), (a_CONSTANTunde_punde_a))) = (''a'')))"
assumes v'84: "((((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<in> ((SUBSET (a_CONSTANTunde_Procunde_a))))) & (((a_CONSTANTunde_punde_a) \<in> (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))) & (\<forall> a_CONSTANTunde_qunde_a \<in> (((a_CONSTANTunde_Procunde_a) \\ ({(a_CONSTANTunde_punde_a)}))) : (((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_qunde_a)))))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))))))) | (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_qunde_a))))))))"
assumes v'85: "((((a_VARIABLEunde_knownunde_hash_primea :: c)) = ([(a_VARIABLEunde_knownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (((fapply ((a_VARIABLEunde_knownunde_a), (a_CONSTANTunde_punde_a))) \<union> ((UNION (setOfAll((Nat), %a_CONSTANTunde_iunde_a. (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))))])))"
assumes v'86: "((((a_VARIABLEunde_notKnownunde_hash_primea :: c)) = ([(a_VARIABLEunde_notKnownunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (subsetOf(((isa_peri_peri_a (((0)), ((a_CONSTANTunde_Cardinalityunde_a ((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))))))))), %a_CONSTANTunde_iunde_a. (((fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) \<noteq> (fapply ((a_VARIABLEunde_A1unde_a), (a_CONSTANTunde_iunde_a)))))))])))"
assumes v'87: "(((fapply (((a_VARIABLEunde_notKnownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a))) = ({})))"
assumes v'88: "((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (fapply (((a_VARIABLEunde_knownunde_hash_primea :: c)), (a_CONSTANTunde_punde_a)))])))"
assumes v'89: "((((a_VARIABLEunde_pcunde_hash_primea :: c)) = ([(a_VARIABLEunde_pcunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (''Done'')])))"
assumes v'90: "((((a_VARIABLEunde_A1unde_hash_primea :: c)) = (a_VARIABLEunde_A1unde_a)))"
shows "(\<exists> a_CONSTANTunde_Punde_a \<in> (subsetOf(((SUBSET (a_CONSTANTunde_Procunde_a))), %a_CONSTANTunde_Qunde_a. ((((a_CONSTANTunde_punde_a) \<in> (a_CONSTANTunde_Qunde_a))) & (\<forall> a_CONSTANTunde_qunde_a \<in> (((a_CONSTANTunde_Procunde_a) \\ ({(a_CONSTANTunde_punde_a)}))) : (((((a_CONSTANTunde_Cardinalityunde_a ((fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_qunde_a)))))) \<noteq> ((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_Qunde_a)))))) | (((a_CONSTANTunde_Qunde_a) = (fapply ((a_VARIABLEunde_resultunde_a), (a_CONSTANTunde_qunde_a)))))))))) : ((((a_VARIABLEunde_resultunde_hash_primea :: c)) = ([(a_VARIABLEunde_resultunde_a) EXCEPT ![(a_CONSTANTunde_punde_a)] = (a_CONSTANTunde_Punde_a)]))))"(is "PROP ?ob'898")
proof -
ML_command {* writeln "*** TLAPS ENTER 898"; *}
show "PROP ?ob'898"

(* BEGIN ZENON INPUT
;; file=.tlacache/GFX_test.tlaps/tlapm_8af170.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/GFX_test.tlaps/tlapm_8af170.znn.out
;; obligation #898
$hyp "v'65" a_STATEunde_Invunde_a
$hyp "v'66" hdb2fe
$hyp "v'67" (\/ a_ACTIONunde_Nextunde_a (= h6fbaa
a_STATEunde_varsunde_a))
$hyp "a_CONSTANTunde_punde_a_in" (TLA.in a_CONSTANTunde_punde_a a_CONSTANTunde_Procunde_a)
$hyp "v'75" (= (TLA.fapply a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a)
"a")
$hyp "v'84" (/\ (TLA.in (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.SUBSET a_CONSTANTunde_Procunde_a)) (TLA.in a_CONSTANTunde_punde_a
(TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))
(TLA.bAll (TLA.setminus a_CONSTANTunde_Procunde_a
(TLA.set a_CONSTANTunde_punde_a)) ((a_CONSTANTunde_qunde_a) (\/ (-. (= (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))))
(= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_qunde_a))))))
$hyp "v'85" (= a_VARIABLEunde_knownunde_hash_primea
(TLA.except a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a (TLA.cup (TLA.fapply a_VARIABLEunde_knownunde_a a_CONSTANTunde_punde_a)
(TLA.UNION (TLA.setOfAll arith.N ((a_CONSTANTunde_iunde_a) (TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'86" (= a_VARIABLEunde_notKnownunde_hash_primea
(TLA.except a_VARIABLEunde_notKnownunde_a a_CONSTANTunde_punde_a (TLA.subsetOf (arith.intrange 0
(a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a))) ((a_CONSTANTunde_iunde_a) (-. (= (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)
(TLA.fapply a_VARIABLEunde_A1unde_a a_CONSTANTunde_iunde_a)))))))
$hyp "v'87" (= (TLA.fapply a_VARIABLEunde_notKnownunde_hash_primea a_CONSTANTunde_punde_a)
TLA.emptyset)
$hyp "v'88" (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a (TLA.fapply a_VARIABLEunde_knownunde_hash_primea a_CONSTANTunde_punde_a)))
$hyp "v'89" (= a_VARIABLEunde_pcunde_hash_primea
(TLA.except a_VARIABLEunde_pcunde_a a_CONSTANTunde_punde_a "Done"))
$hyp "v'90" (= a_VARIABLEunde_A1unde_hash_primea
a_VARIABLEunde_A1unde_a)
$goal (TLA.bEx (TLA.subsetOf (TLA.SUBSET a_CONSTANTunde_Procunde_a) ((a_CONSTANTunde_Qunde_a) (/\ (TLA.in a_CONSTANTunde_punde_a
a_CONSTANTunde_Qunde_a) (TLA.bAll (TLA.setminus a_CONSTANTunde_Procunde_a
(TLA.set a_CONSTANTunde_punde_a)) ((a_CONSTANTunde_qunde_a) (\/ (-. (= (a_CONSTANTunde_Cardinalityunde_a (TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_qunde_a))
(a_CONSTANTunde_Cardinalityunde_a a_CONSTANTunde_Qunde_a)))
(= a_CONSTANTunde_Qunde_a
(TLA.fapply a_VARIABLEunde_resultunde_a a_CONSTANTunde_qunde_a)))))))) ((a_CONSTANTunde_Punde_a) (= a_VARIABLEunde_resultunde_hash_primea
(TLA.except a_VARIABLEunde_resultunde_a a_CONSTANTunde_punde_a a_CONSTANTunde_Punde_a))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"(((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]) \\in SUBSET(a_CONSTANTunde_Procunde_a))&((a_CONSTANTunde_punde_a \\in (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))|((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))" (is "?z_hn&?z_ht")
 using v'84 by blast
 have z_Hj:"(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, (a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])))" (is "_=?z_hbi")
 using v'88 by blast
 assume z_Hm:"(~bEx(subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))), (\<lambda>a_CONSTANTunde_Punde_a. (a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, a_CONSTANTunde_Punde_a)))))" (is "~?z_hbj")
 have z_Hn: "?z_hn"
 by (rule zenon_and_0 [OF z_Hf])
 have z_Ht: "?z_ht" (is "?z_hu&?z_hv")
 by (rule zenon_and_1 [OF z_Hf])
 have z_Hu: "?z_hu"
 by (rule zenon_and_0 [OF z_Ht])
 have z_Hv: "?z_hv"
 by (rule zenon_and_1 [OF z_Ht])
 have z_Hbz_z_Hm: "(~(\\E x:((x \\in subsetOf(SUBSET(a_CONSTANTunde_Procunde_a), (\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))))&(a_VARIABLEunde_resultunde_hash_primea=except(a_VARIABLEunde_resultunde_a, a_CONSTANTunde_punde_a, x))))) == (~?z_hbj)" (is "?z_hbz == ?z_hm")
 by (unfold bEx_def)
 have z_Hbz: "?z_hbz" (is "~(\\E x : ?z_hcg(x))")
 by (unfold z_Hbz_z_Hm, fact z_Hm)
 have z_Hch: "~?z_hcg((a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a]))" (is "~(?z_hci&?z_hj)")
 by (rule zenon_notex_0 [of "?z_hcg" "(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])", OF z_Hbz])
 show FALSE
 proof (rule zenon_notand [OF z_Hch])
  assume z_Hcj:"(~?z_hci)"
  show FALSE
  proof (rule zenon_notin_subsetof [of "(a_VARIABLEunde_knownunde_hash_primea[a_CONSTANTunde_punde_a])" "SUBSET(a_CONSTANTunde_Procunde_a)" "(\<lambda>a_CONSTANTunde_Qunde_a. ((a_CONSTANTunde_punde_a \\in a_CONSTANTunde_Qunde_a)&bAll((a_CONSTANTunde_Procunde_a \\ {a_CONSTANTunde_punde_a}), (\<lambda>a_CONSTANTunde_qunde_a. ((a_CONSTANTunde_Cardinalityunde_a((a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a]))~=a_CONSTANTunde_Cardinalityunde_a(a_CONSTANTunde_Qunde_a))|(a_CONSTANTunde_Qunde_a=(a_VARIABLEunde_resultunde_a[a_CONSTANTunde_qunde_a])))))))", OF z_Hcj])
   assume z_Hck:"(~?z_hn)"
   show FALSE
   by (rule notE [OF z_Hck z_Hn])
  next
   assume z_Hcl:"(~?z_ht)"
   show FALSE
   proof (rule zenon_notand [OF z_Hcl])
    assume z_Hcm:"(~?z_hu)"
    show FALSE
    by (rule notE [OF z_Hcm z_Hu])
   next
    assume z_Hcn:"(~?z_hv)"
    show FALSE
    by (rule notE [OF z_Hcn z_Hv])
   qed
  qed
 next
  assume z_Hco:"(a_VARIABLEunde_resultunde_hash_primea~=?z_hbi)"
  show FALSE
  by (rule notE [OF z_Hco z_Hj])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 898"; *} qed
end

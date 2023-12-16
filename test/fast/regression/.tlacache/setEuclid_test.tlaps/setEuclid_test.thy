(* automatically generated -- do not edit manually *)
theory setEuclid_test imports Constant Zenon begin
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

lemma ob'46:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Inputunde_a
fixes a_CONSTANTunde_defaultInitValueunde_a
fixes a_VARIABLEunde_Sunde_a a_VARIABLEunde_Sunde_a'
fixes a_VARIABLEunde_gcdunde_a a_VARIABLEunde_gcdunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_Max_ suppressed *)
(* usable definition CONSTANT_|_ suppressed *)
(* usable definition CONSTANT_GCD_ suppressed *)
assumes v'27: "((((((a_VARIABLEunde_Sunde_a) \<subseteq> (((Nat) \\ ({((0))}))))) & (((a_VARIABLEunde_Sunde_a) \<noteq> ({}))) & ((a_CONSTANTunde_IsFiniteSetunde_a ((a_VARIABLEunde_Sunde_a))))) & (((((a_VARIABLEunde_pcunde_a) = (''Done''))) \<Rightarrow> (((a_VARIABLEunde_gcdunde_a) \<in> (((Nat) \\ ({((0))}))))))) & (((a_VARIABLEunde_pcunde_a) \<in> ({(''lbl''), (''Done'')})))) & (((((a_VARIABLEunde_pcunde_a) = (''Done''))) \<Rightarrow> (((a_VARIABLEunde_gcdunde_a) = ((a_CONSTANTunde_GCDunde_a ((a_CONSTANTunde_Inputunde_a)))))))))"
assumes v'28: "((((a_CONSTANTunde_GCDunde_a ((a_VARIABLEunde_Sunde_a)))) = ((a_CONSTANTunde_GCDunde_a ((a_CONSTANTunde_Inputunde_a))))))"
assumes v'29: "(a_ACTIONunde_Nextunde_a)"
shows "(((bChoice((a_VARIABLEunde_Sunde_a), %a_CONSTANTunde_tunde_a. (TRUE))) \<in> (((Nat) \\ ({((0))})))))"(is "PROP ?ob'46")
proof -
ML_command {* writeln "*** TLAPS ENTER 46"; *}
show "PROP ?ob'46"

(* BEGIN ZENON INPUT
;; file=.tlacache/setEuclid_test.tlaps/tlapm_524494.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/setEuclid_test.tlaps/tlapm_524494.znn.out
;; obligation #46
$hyp "v'27" (/\ (/\ (/\ (TLA.subseteq a_VARIABLEunde_Sunde_a
(TLA.setminus arith.N (TLA.set 0))) (-. (= a_VARIABLEunde_Sunde_a
TLA.emptyset)) (a_CONSTANTunde_IsFiniteSetunde_a a_VARIABLEunde_Sunde_a))
(=> (= a_VARIABLEunde_pcunde_a "Done") (TLA.in a_VARIABLEunde_gcdunde_a
(TLA.setminus arith.N (TLA.set 0)))) (TLA.in a_VARIABLEunde_pcunde_a
(TLA.set "lbl" "Done"))) (=> (= a_VARIABLEunde_pcunde_a "Done")
(= a_VARIABLEunde_gcdunde_a
(a_CONSTANTunde_GCDunde_a a_CONSTANTunde_Inputunde_a))))
$hyp "v'28" (= (a_CONSTANTunde_GCDunde_a a_VARIABLEunde_Sunde_a)
(a_CONSTANTunde_GCDunde_a a_CONSTANTunde_Inputunde_a))
$hyp "v'29" a_ACTIONunde_Nextunde_a
$goal (TLA.in (TLA.bChoice a_VARIABLEunde_Sunde_a ((a_CONSTANTunde_tunde_a) T.))
(TLA.setminus arith.N
(TLA.set 0)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_VARIABLEunde_Sunde_a \\subseteq (Nat \\ {0}))&((a_VARIABLEunde_Sunde_a~={})&a_CONSTANTunde_IsFiniteSetunde_a(a_VARIABLEunde_Sunde_a)))&(((a_VARIABLEunde_pcunde_a=''Done'')=>(a_VARIABLEunde_gcdunde_a \\in (Nat \\ {0})))&(a_VARIABLEunde_pcunde_a \\in {''lbl'', ''Done''})))&((a_VARIABLEunde_pcunde_a=''Done'')=>(a_VARIABLEunde_gcdunde_a=a_CONSTANTunde_GCDunde_a(a_CONSTANTunde_Inputunde_a))))" (is "?z_he&?z_hba")
 using v'27 by blast
 assume z_Hd:"(~(bChoice(a_VARIABLEunde_Sunde_a, (\<lambda>a_CONSTANTunde_tunde_a. TRUE)) \\in (Nat \\ {0})))" (is "~?z_hbe")
 have z_He: "?z_he" (is "?z_hf&?z_hq")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hf: "?z_hf" (is "?z_hg&?z_hm")
 by (rule zenon_and_0 [OF z_He])
 have z_Hg: "?z_hg"
 by (rule zenon_and_0 [OF z_Hf])
 have z_Hm: "?z_hm" (is "?z_hn&?z_hp")
 by (rule zenon_and_1 [OF z_Hf])
 have z_Hn: "?z_hn"
 by (rule zenon_and_0 [OF z_Hm])
 have z_Hbi_z_Hg: "bAll(a_VARIABLEunde_Sunde_a, (\<lambda>x. (x \\in (Nat \\ {0})))) == ?z_hg" (is "?z_hbi == _")
 by (unfold subset_def)
 have z_Hbi: "?z_hbi"
 by (unfold z_Hbi_z_Hg, fact z_Hg)
 have z_Hbm_z_Hbi: "(\\A x:((x \\in a_VARIABLEunde_Sunde_a)=>(x \\in (Nat \\ {0})))) == ?z_hbi" (is "?z_hbm == _")
 by (unfold bAll_def)
 have z_Hbm: "?z_hbm" (is "\\A x : ?z_hbp(x)")
 by (unfold z_Hbm_z_Hbi, fact z_Hbi)
 have z_Hbq_z_Hd: "(~((CHOOSE x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE)) \\in (Nat \\ {0}))) == (~?z_hbe)" (is "?z_hbq == ?z_hd")
 by (unfold bChoose_def)
 have z_Hbq: "?z_hbq" (is "~?z_hbr")
 by (unfold z_Hbq_z_Hd, fact z_Hd)
 show FALSE
 proof (rule zenon_em [of "(\\E x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE))"])
  assume z_Hbu:"(\\E x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE))" (is "\\E x : ?z_hbv(x)")
  have z_Hbw: "?z_hbv((CHOOSE x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE)))" (is "?z_hbx&?z_hbh")
  by (rule zenon_ex_choose_0 [of "?z_hbv", OF z_Hbu])
  have z_Hbx: "?z_hbx"
  by (rule zenon_and_0 [OF z_Hbw])
  have z_Hby: "?z_hbp((CHOOSE x:((x \\in a_VARIABLEunde_Sunde_a)&?z_hbh)))"
  by (rule zenon_all_0 [of "?z_hbp" "(CHOOSE x:((x \\in a_VARIABLEunde_Sunde_a)&?z_hbh))", OF z_Hbm])
  show FALSE
  proof (rule zenon_imply [OF z_Hby])
   assume z_Hbz:"(~?z_hbx)"
   show FALSE
   by (rule notE [OF z_Hbz z_Hbx])
  next
   assume z_Hbr:"?z_hbr"
   show FALSE
   by (rule notE [OF z_Hbq z_Hbr])
  qed
 next
  assume z_Hca:"(~(\\E x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE)))" (is "~(\\E x : ?z_hbv(x))")
  have z_Hcb: "(~(\\A zenon_Vq:((zenon_Vq \\in a_VARIABLEunde_Sunde_a)<=>(zenon_Vq \\in {}))))" (is "~(\\A x : ?z_hch(x))")
  by (rule zenon_notsetequal_0 [of "a_VARIABLEunde_Sunde_a" "{}", OF z_Hn])
  have z_Hci: "(\\E zenon_Vq:(~((zenon_Vq \\in a_VARIABLEunde_Sunde_a)<=>(zenon_Vq \\in {}))))" (is "\\E x : ?z_hck(x)")
  by (rule zenon_notallex_0 [of "?z_hch", OF z_Hcb])
  have z_Hcl: "?z_hck((CHOOSE zenon_Vq:(~((zenon_Vq \\in a_VARIABLEunde_Sunde_a)<=>(zenon_Vq \\in {})))))" (is "~(?z_hcn<=>?z_hco)")
  by (rule zenon_ex_choose_0 [of "?z_hck", OF z_Hci])
  show FALSE
  proof (rule zenon_notequiv [OF z_Hcl])
   assume z_Hcp:"(~?z_hcn)"
   assume z_Hco:"?z_hco"
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vq:(~((zenon_Vq \\in a_VARIABLEunde_Sunde_a)<=>(zenon_Vq \\in {}))))", OF z_Hco])
  next
   assume z_Hcn:"?z_hcn"
   assume z_Hcq:"(~?z_hco)"
   have z_Hcr: "~?z_hbv((CHOOSE zenon_Vq:(~((zenon_Vq \\in a_VARIABLEunde_Sunde_a)<=>(zenon_Vq \\in {})))))" (is "~(_&?z_hbh)")
   by (rule zenon_notex_0 [of "?z_hbv" "(CHOOSE zenon_Vq:(~((zenon_Vq \\in a_VARIABLEunde_Sunde_a)<=>(zenon_Vq \\in {}))))", OF z_Hca])
   show FALSE
   proof (rule zenon_notand [OF z_Hcr])
    assume z_Hcp:"(~?z_hcn)"
    show FALSE
    by (rule notE [OF z_Hcp z_Hcn])
   next
    assume z_Hcs:"(~?z_hbh)"
    show FALSE
    by (rule zenon_nottrue [OF z_Hcs])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 46"; *} qed
lemma ob'100:
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Inputunde_a
fixes a_CONSTANTunde_defaultInitValueunde_a
fixes a_VARIABLEunde_Sunde_a a_VARIABLEunde_Sunde_a'
fixes a_VARIABLEunde_gcdunde_a a_VARIABLEunde_gcdunde_a'
fixes a_VARIABLEunde_pcunde_a a_VARIABLEunde_pcunde_a'
(* usable definition STATE_vars_ suppressed *)
(* usable definition STATE_Init_ suppressed *)
(* usable definition ACTION_lbl_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition STATE_Termination_ suppressed *)
(* usable definition CONSTANT_Max_ suppressed *)
(* usable definition CONSTANT_|_ suppressed *)
(* usable definition CONSTANT_GCD_ suppressed *)
(* usable definition STATE_CorrectTermination_ suppressed *)
assumes v'29: "((((((a_VARIABLEunde_Sunde_a) \<subseteq> (((Nat) \\ ({((0))}))))) & (((a_VARIABLEunde_Sunde_a) \<noteq> ({}))) & ((a_CONSTANTunde_IsFiniteSetunde_a ((a_VARIABLEunde_Sunde_a))))) & (((((a_VARIABLEunde_pcunde_a) = (''Done''))) \<Rightarrow> (((a_VARIABLEunde_gcdunde_a) \<in> (((Nat) \\ ({((0))}))))))) & (((a_VARIABLEunde_pcunde_a) \<in> ({(''lbl''), (''Done'')})))) & (a_STATEunde_CorrectTerminationunde_a))"
assumes v'30: "((((a_CONSTANTunde_GCDunde_a ((a_VARIABLEunde_Sunde_a)))) = ((a_CONSTANTunde_GCDunde_a ((a_CONSTANTunde_Inputunde_a))))))"
assumes v'31: "(a_ACTIONunde_Nextunde_a)"
assumes v'44: "((((((a_CONSTANTunde_Cardinalityunde_a ((a_VARIABLEunde_Sunde_a)))) = ((Succ[0])))) \<Rightarrow> (((a_VARIABLEunde_Sunde_a) = ({(bChoice((a_VARIABLEunde_Sunde_a), %a_CONSTANTunde_tunde_a. (TRUE)))})))))"
assumes v'45: "(\<forall> a_CONSTANTunde_xunde_a \<in> (((Nat) \\ ({((0))}))) : ((((a_CONSTANTunde_GCDunde_a (({(a_CONSTANTunde_xunde_a)})))) = (a_CONSTANTunde_xunde_a))))"
shows "((((((a_CONSTANTunde_Cardinalityunde_a ((a_VARIABLEunde_Sunde_a)))) = ((Succ[0])))) \<Rightarrow> ((((a_CONSTANTunde_GCDunde_a ((a_VARIABLEunde_Sunde_a)))) = (bChoice((a_VARIABLEunde_Sunde_a), %a_CONSTANTunde_tunde_a. (TRUE)))))))"(is "PROP ?ob'100")
proof -
ML_command {* writeln "*** TLAPS ENTER 100"; *}
show "PROP ?ob'100"

(* BEGIN ZENON INPUT
;; file=.tlacache/setEuclid_test.tlaps/tlapm_0457c3.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/setEuclid_test.tlaps/tlapm_0457c3.znn.out
;; obligation #100
$hyp "v'29" (/\ (/\ (/\ (TLA.subseteq a_VARIABLEunde_Sunde_a
(TLA.setminus arith.N (TLA.set 0))) (-. (= a_VARIABLEunde_Sunde_a
TLA.emptyset)) (a_CONSTANTunde_IsFiniteSetunde_a a_VARIABLEunde_Sunde_a))
(=> (= a_VARIABLEunde_pcunde_a "Done") (TLA.in a_VARIABLEunde_gcdunde_a
(TLA.setminus arith.N (TLA.set 0)))) (TLA.in a_VARIABLEunde_pcunde_a
(TLA.set "lbl" "Done")))
a_STATEunde_CorrectTerminationunde_a)
$hyp "v'30" (= (a_CONSTANTunde_GCDunde_a a_VARIABLEunde_Sunde_a)
(a_CONSTANTunde_GCDunde_a a_CONSTANTunde_Inputunde_a))
$hyp "v'31" a_ACTIONunde_Nextunde_a
$hyp "v'44" (=> (= (a_CONSTANTunde_Cardinalityunde_a a_VARIABLEunde_Sunde_a)
(TLA.fapply TLA.Succ 0)) (= a_VARIABLEunde_Sunde_a
(TLA.set (TLA.bChoice a_VARIABLEunde_Sunde_a ((a_CONSTANTunde_tunde_a) T.)))))
$hyp "v'45" (TLA.bAll (TLA.setminus arith.N
(TLA.set 0)) ((a_CONSTANTunde_xunde_a) (= (a_CONSTANTunde_GCDunde_a (TLA.set a_CONSTANTunde_xunde_a))
a_CONSTANTunde_xunde_a)))
$goal (=> (= (a_CONSTANTunde_Cardinalityunde_a a_VARIABLEunde_Sunde_a)
(TLA.fapply TLA.Succ 0)) (= (a_CONSTANTunde_GCDunde_a a_VARIABLEunde_Sunde_a)
(TLA.bChoice a_VARIABLEunde_Sunde_a ((a_CONSTANTunde_tunde_a) T.))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((a_VARIABLEunde_Sunde_a \\subseteq (Nat \\ {0}))&((a_VARIABLEunde_Sunde_a~={})&a_CONSTANTunde_IsFiniteSetunde_a(a_VARIABLEunde_Sunde_a)))&(((a_VARIABLEunde_pcunde_a=''Done'')=>(a_VARIABLEunde_gcdunde_a \\in (Nat \\ {0})))&(a_VARIABLEunde_pcunde_a \\in {''lbl'', ''Done''})))&a_STATEunde_CorrectTerminationunde_a)" (is "?z_hg&_")
 using v'29 by blast
 have z_He:"bAll((Nat \\ {0}), (\<lambda>a_CONSTANTunde_xunde_a. (a_CONSTANTunde_GCDunde_a({a_CONSTANTunde_xunde_a})=a_CONSTANTunde_xunde_a)))" (is "?z_he")
 using v'45 by blast
 have z_Hd:"((a_CONSTANTunde_Cardinalityunde_a(a_VARIABLEunde_Sunde_a)=1)=>(a_VARIABLEunde_Sunde_a={bChoice(a_VARIABLEunde_Sunde_a, (\<lambda>a_CONSTANTunde_tunde_a. TRUE))}))" (is "?z_hbi=>?z_hbl")
 using v'44 by blast
 assume z_Hf:"(~(?z_hbi=>(a_CONSTANTunde_GCDunde_a(a_VARIABLEunde_Sunde_a)=bChoice(a_VARIABLEunde_Sunde_a, (\<lambda>a_CONSTANTunde_tunde_a. TRUE)))))" (is "~(_=>?z_hbr)")
 have z_Hg: "?z_hg" (is "?z_hh&?z_hs")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hh: "?z_hh" (is "?z_hi&?z_ho")
 by (rule zenon_and_0 [OF z_Hg])
 have z_Hi: "?z_hi"
 by (rule zenon_and_0 [OF z_Hh])
 have z_Hbt_z_Hi: "bAll(a_VARIABLEunde_Sunde_a, (\<lambda>x. (x \\in (Nat \\ {0})))) == ?z_hi" (is "?z_hbt == _")
 by (unfold subset_def)
 have z_Hbt: "?z_hbt"
 by (unfold z_Hbt_z_Hi, fact z_Hi)
 have z_Hbx_z_Hbt: "(\\A x:((x \\in a_VARIABLEunde_Sunde_a)=>(x \\in (Nat \\ {0})))) == ?z_hbt" (is "?z_hbx == _")
 by (unfold bAll_def)
 have z_Hbx: "?z_hbx" (is "\\A x : ?z_hca(x)")
 by (unfold z_Hbx_z_Hbt, fact z_Hbt)
 have z_Hcb_z_He: "(\\A x:((x \\in (Nat \\ {0}))=>(a_CONSTANTunde_GCDunde_a({x})=x))) == ?z_he" (is "?z_hcb == _")
 by (unfold bAll_def)
 have z_Hcb: "?z_hcb" (is "\\A x : ?z_hcg(x)")
 by (unfold z_Hcb_z_He, fact z_He)
 have z_Hbi: "?z_hbi" (is "?z_hbj=?z_hbk")
 by (rule zenon_notimply_0 [OF z_Hf])
 have z_Hch: "(a_CONSTANTunde_GCDunde_a(a_VARIABLEunde_Sunde_a)~=bChoice(a_VARIABLEunde_Sunde_a, (\<lambda>a_CONSTANTunde_tunde_a. TRUE)))" (is "?z_hbs~=?z_hbn")
 by (rule zenon_notimply_1 [OF z_Hf])
 have z_Hci_z_Hch: "(?z_hbs~=(CHOOSE x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE))) == (?z_hbs~=?z_hbn)" (is "?z_hci == ?z_hch")
 by (unfold bChoose_def)
 have z_Hci: "?z_hci" (is "_~=?z_hcj")
 by (unfold z_Hci_z_Hch, fact z_Hch)
 show FALSE
 proof (rule zenon_imply [OF z_Hd])
  assume z_Hcl:"(?z_hbj~=?z_hbk)"
  show FALSE
  by (rule notE [OF z_Hcl z_Hbi])
 next
  assume z_Hbl:"?z_hbl" (is "_=?z_hbm")
  have z_Hcm_z_Hbl: "(a_VARIABLEunde_Sunde_a={?z_hcj}) == ?z_hbl" (is "?z_hcm == _")
  by (unfold bChoose_def)
  have z_Hcm: "?z_hcm" (is "_=?z_hcn")
  by (unfold z_Hcm_z_Hbl, fact z_Hbl)
  show FALSE
  proof (rule zenon_em [of "(\\E x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE))"])
   assume z_Hco:"(\\E x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE))" (is "\\E x : ?z_hcp(x)")
   have z_Hcq: "?z_hcp(?z_hcj)" (is "?z_hcr&?z_hbp")
   by (rule zenon_ex_choose_0 [of "?z_hcp", OF z_Hco])
   have z_Hcr: "?z_hcr"
   by (rule zenon_and_0 [OF z_Hcq])
   have z_Hcs: "?z_hcg(?z_hcj)" (is "?z_hct=>?z_hcu")
   by (rule zenon_all_0 [of "?z_hcg" "?z_hcj", OF z_Hcb])
   show FALSE
   proof (rule zenon_imply [OF z_Hcs])
    assume z_Hcv:"(~?z_hct)"
    have z_Hcw: "?z_hca(?z_hcj)"
    by (rule zenon_all_0 [of "?z_hca" "?z_hcj", OF z_Hbx])
    show FALSE
    proof (rule zenon_imply [OF z_Hcw])
     assume z_Hcx:"(~?z_hcr)"
     show FALSE
     by (rule notE [OF z_Hcx z_Hcr])
    next
     assume z_Hct:"?z_hct"
     show FALSE
     by (rule notE [OF z_Hcv z_Hct])
    qed
   next
    assume z_Hcu:"?z_hcu" (is "?z_hcy=_")
    show FALSE
    proof (rule notE [OF z_Hci])
     have z_Hcz: "(?z_hcy=?z_hbs)"
     proof (rule zenon_nnpp [of "(?z_hcy=?z_hbs)"])
      assume z_Hda:"(?z_hcy~=?z_hbs)"
      show FALSE
      proof (rule zenon_em [of "(?z_hbs=?z_hbs)"])
       assume z_Hdb:"(?z_hbs=?z_hbs)"
       show FALSE
       proof (rule notE [OF z_Hda])
        have z_Hdc: "(?z_hbs=?z_hcy)"
        proof (rule zenon_nnpp [of "(?z_hbs=?z_hcy)"])
         assume z_Hdd:"(?z_hbs~=?z_hcy)"
         show FALSE
         proof (rule zenon_noteq [of "?z_hcy"])
          have z_Hde: "(?z_hcy~=?z_hcy)"
          by (rule subst [where P="(\<lambda>zenon_Vaf. (a_CONSTANTunde_GCDunde_a(zenon_Vaf)~=?z_hcy))", OF z_Hcm], fact z_Hdd)
          thus "(?z_hcy~=?z_hcy)" .
         qed
        qed
        have z_Hcz: "(?z_hcy=?z_hbs)"
        by (rule subst [where P="(\<lambda>zenon_Vof. (zenon_Vof=?z_hbs))", OF z_Hdc], fact z_Hdb)
        thus "(?z_hcy=?z_hbs)" .
       qed
      next
       assume z_Hdm:"(?z_hbs~=?z_hbs)"
       show FALSE
       by (rule zenon_noteq [OF z_Hdm])
      qed
     qed
     have z_Hdn: "(?z_hbs=?z_hcj)"
     by (rule subst [where P="(\<lambda>zenon_Vte. (zenon_Vte=?z_hcj))", OF z_Hcz], fact z_Hcu)
     thus "(?z_hbs=?z_hcj)" .
    qed
   qed
  next
   assume z_Hdr:"(~(\\E x:((x \\in a_VARIABLEunde_Sunde_a)&TRUE)))" (is "~(\\E x : ?z_hcp(x))")
   have z_Hds: "~?z_hcp(?z_hcj)" (is "~(?z_hcr&?z_hbp)")
   by (rule zenon_notex_0 [of "?z_hcp" "?z_hcj", OF z_Hdr])
   show FALSE
   proof (rule zenon_notand [OF z_Hds])
    assume z_Hcx:"(~?z_hcr)"
    have z_Hdt: "(~(?z_hcj \\in ?z_hbm))" (is "~?z_hdu")
    by (rule subst [where P="(\<lambda>zenon_Vad. (~(?z_hcj \\in zenon_Vad)))", OF z_Hbl z_Hcx])
    have z_Hdz: "(?z_hcj~=?z_hbn)"
    by (rule zenon_notin_addElt_0 [of "?z_hcj" "?z_hbn" "{}", OF z_Hdt])
    have z_Heb_z_Hdz: "(?z_hcj~=?z_hcj) == (?z_hcj~=?z_hbn)" (is "?z_heb == ?z_hdz")
    by (unfold bChoose_def)
    have z_Heb: "?z_heb"
    by (unfold z_Heb_z_Hdz, fact z_Hdz)
    show FALSE
    by (rule zenon_noteq [OF z_Heb])
   next
    assume z_Hec:"(~?z_hbp)"
    show FALSE
    by (rule zenon_nottrue [OF z_Hec])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 100"; *} qed
end

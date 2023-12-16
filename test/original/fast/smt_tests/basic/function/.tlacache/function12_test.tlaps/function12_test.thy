(* automatically generated -- do not edit manually *)
theory function12_test imports Constant Zenon begin
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

lemma ob'1:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Aunde_a
fixes a_CONSTANTunde_Bunde_a
fixes a_CONSTANTunde_funde_a
assumes v'7: "((((DOMAIN (a_CONSTANTunde_funde_a))) = (a_CONSTANTunde_Aunde_a)))"
assumes v'8: "(\<forall> a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Aunde_a) : (((fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))) \<in> (a_CONSTANTunde_Bunde_a))))"
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> (a_CONSTANTunde_Aunde_a))"
fixes a_CONSTANTunde_Eunde_a
assumes v'11: "((((a_CONSTANTunde_Eunde_a ((a_CONSTANTunde_xunde_a)))) \<in> (a_CONSTANTunde_Bunde_a)))"
shows "((([(a_CONSTANTunde_funde_a) EXCEPT ![(a_CONSTANTunde_xunde_a)] = ((a_CONSTANTunde_Eunde_a ((a_CONSTANTunde_xunde_a))))]) \<in> ([(a_CONSTANTunde_Aunde_a) \<rightarrow> (a_CONSTANTunde_Bunde_a)])))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/function12_test.tlaps/tlapm_ae293a.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/function12_test.tlaps/tlapm_ae293a.znn.out
;; obligation #1
$hyp "v'7" (= (TLA.DOMAIN a_CONSTANTunde_funde_a)
a_CONSTANTunde_Aunde_a)
$hyp "v'8" (TLA.bAll a_CONSTANTunde_Aunde_a ((a_CONSTANTunde_xunde_a) (TLA.in (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a)
a_CONSTANTunde_Bunde_a)))
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a a_CONSTANTunde_Aunde_a)
$hyp "v'11" (TLA.in (a_CONSTANTunde_Eunde_a a_CONSTANTunde_xunde_a)
a_CONSTANTunde_Bunde_a)
$goal (TLA.in (TLA.except a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a (a_CONSTANTunde_Eunde_a a_CONSTANTunde_xunde_a))
(TLA.FuncSet a_CONSTANTunde_Aunde_a a_CONSTANTunde_Bunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(DOMAIN(a_CONSTANTunde_funde_a)=a_CONSTANTunde_Aunde_a)" (is "?z_hf=_")
 using v'7 by blast
 have z_Hb:"bAll(a_CONSTANTunde_Aunde_a, (\<lambda>a_CONSTANTunde_xunde_a. ((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]) \\in a_CONSTANTunde_Bunde_a)))" (is "?z_hb")
 using v'8 by blast
 have z_Hd:"(a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a) \\in a_CONSTANTunde_Bunde_a)" (is "?z_hd")
 using v'11 by blast
 have zenon_L1_: "(~isAFcn(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)))) ==> FALSE" (is "?z_ho ==> FALSE")
 proof -
  assume z_Ho:"?z_ho" (is "~?z_hp")
  show FALSE
  by (rule zenon_notisafcn_except [of "a_CONSTANTunde_funde_a" "a_CONSTANTunde_xunde_a" "a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)", OF z_Ho])
 qed
 have zenon_L2_: "(DOMAIN(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)))~=?z_hf) ==> FALSE" (is "?z_hr ==> FALSE")
 proof -
  assume z_Hr:"?z_hr" (is "?z_hs~=_")
  have z_Ht: "(?z_hf~=?z_hf)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vkc. (zenon_Vkc~=?z_hf))" "a_CONSTANTunde_funde_a" "a_CONSTANTunde_xunde_a" "a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)", OF z_Hr])
  show FALSE
  by (rule zenon_noteq [OF z_Ht])
 qed
 have zenon_L3_: "(?z_hf=a_CONSTANTunde_Aunde_a) ==> (\\A x:((x \\in a_CONSTANTunde_Aunde_a)=>((a_CONSTANTunde_funde_a[x]) \\in a_CONSTANTunde_Bunde_a))) ==> ((CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a)))) \\in ?z_hf) ==> (~((a_CONSTANTunde_funde_a[(CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a))))]) \\in a_CONSTANTunde_Bunde_a)) ==> FALSE" (is "?z_ha ==> ?z_hx ==> ?z_hbd ==> ?z_hbl ==> FALSE")
 proof -
  assume z_Ha:"?z_ha"
  assume z_Hx:"?z_hx" (is "\\A x : ?z_hbo(x)")
  assume z_Hbd:"?z_hbd"
  assume z_Hbl:"?z_hbl" (is "~?z_hbm")
  have z_Hbp: "?z_hbo((CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a)))))" (is "?z_hbq=>_")
  by (rule zenon_all_0 [of "?z_hbo" "(CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a))))", OF z_Hx])
  show FALSE
  proof (rule zenon_imply [OF z_Hbp])
   assume z_Hbr:"(~?z_hbq)"
   have z_Hbs: "(~?z_hbd)"
   by (rule ssubst [where P="(\<lambda>zenon_Vhc. (~((CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a)))) \\in zenon_Vhc)))", OF z_Ha z_Hbr])
   show FALSE
   by (rule notE [OF z_Hbs z_Hbd])
  next
   assume z_Hbm:"?z_hbm"
   show FALSE
   by (rule notE [OF z_Hbl z_Hbm])
  qed
 qed
 assume z_He:"(~(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)) \\in FuncSet(a_CONSTANTunde_Aunde_a, a_CONSTANTunde_Bunde_a)))" (is "~?z_hbx")
 have z_Hx_z_Hb: "(\\A x:((x \\in a_CONSTANTunde_Aunde_a)=>((a_CONSTANTunde_funde_a[x]) \\in a_CONSTANTunde_Bunde_a))) == ?z_hb" (is "?z_hx == _")
 by (unfold bAll_def)
 have z_Hx: "?z_hx" (is "\\A x : ?z_hbo(x)")
 by (unfold z_Hx_z_Hb, fact z_Hb)
 have z_Hbz: "(~(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)) \\in FuncSet(?z_hf, a_CONSTANTunde_Bunde_a)))" (is "~?z_hca")
 by (rule ssubst [where P="(\<lambda>zenon_Vf. (~(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)) \\in FuncSet(zenon_Vf, a_CONSTANTunde_Bunde_a))))", OF z_Ha z_He])
 show FALSE
 proof (rule zenon_notin_funcset [of "except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))" "?z_hf" "a_CONSTANTunde_Bunde_a", OF z_Hbz])
  assume z_Ho:"(~isAFcn(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))))" (is "~?z_hp")
  show FALSE
  by (rule zenon_L1_ [OF z_Ho])
 next
  assume z_Hr:"(DOMAIN(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)))~=?z_hf)" (is "?z_hs~=_")
  show FALSE
  by (rule zenon_L2_ [OF z_Hr])
 next
  assume z_Hch:"(~(\\A zenon_Vda:((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a))))" (is "~(\\A x : ?z_hcj(x))")
  have z_Hck: "(\\E zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a))))" (is "\\E x : ?z_hcl(x)")
  by (rule zenon_notallex_0 [of "?z_hcj", OF z_Hch])
  have z_Hcm: "?z_hcl((CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a)))))" (is "~(?z_hbd=>?z_hcn)")
  by (rule zenon_ex_choose_0 [of "?z_hcl", OF z_Hck])
  have z_Hbd: "?z_hbd"
  by (rule zenon_notimply_0 [OF z_Hcm])
  have z_Hco: "(~?z_hcn)"
  by (rule zenon_notimply_1 [OF z_Hcm])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Voa. (~(zenon_Voa \\in a_CONSTANTunde_Bunde_a)))" "a_CONSTANTunde_funde_a" "a_CONSTANTunde_xunde_a" "a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a)" "(CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a))))", OF z_Hco])
   assume z_Hbd:"?z_hbd"
   assume z_Hct:"(a_CONSTANTunde_xunde_a=(CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a)))))" (is "_=?z_hbe")
   assume z_Hcu:"(~?z_hd)"
   show FALSE
   by (rule notE [OF z_Hcu z_Hd])
  next
   assume z_Hbd:"?z_hbd"
   assume z_Hcv:"(a_CONSTANTunde_xunde_a~=(CHOOSE zenon_Vda:(~((zenon_Vda \\in ?z_hf)=>((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, a_CONSTANTunde_Eunde_a(a_CONSTANTunde_xunde_a))[zenon_Vda]) \\in a_CONSTANTunde_Bunde_a)))))" (is "_~=?z_hbe")
   assume z_Hbl:"(~((a_CONSTANTunde_funde_a[?z_hbe]) \\in a_CONSTANTunde_Bunde_a))" (is "~?z_hbm")
   show FALSE
   by (rule zenon_L3_ [OF z_Ha z_Hx z_Hbd z_Hbl])
  next
   assume z_Hbs:"(~?z_hbd)"
   show FALSE
   by (rule notE [OF z_Hbs z_Hbd])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

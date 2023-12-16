(* automatically generated -- do not edit manually *)
theory function16_test imports Constant Zenon begin
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
fixes a_CONSTANTunde_funde_a
fixes a_CONSTANTunde_xunde_a
assumes a_CONSTANTunde_xunde_a_in : "(a_CONSTANTunde_xunde_a \<in> ((DOMAIN (a_CONSTANTunde_funde_a))))"
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> ((DOMAIN (fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))))))"
fixes a_CONSTANTunde_uunde_a
assumes a_CONSTANTunde_uunde_a_in : "(a_CONSTANTunde_uunde_a \<in> ((DOMAIN (a_CONSTANTunde_funde_a))))"
fixes a_CONSTANTunde_vunde_a
assumes a_CONSTANTunde_vunde_a_in : "(a_CONSTANTunde_vunde_a \<in> ((DOMAIN (fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_uunde_a))))))"
fixes a_CONSTANTunde_zunde_a
fixes a_CONSTANTunde_wunde_a
assumes v'11: "(((a_CONSTANTunde_uunde_a) \<noteq> (a_CONSTANTunde_xunde_a)))"
shows "(((fapply (([([(a_CONSTANTunde_funde_a) EXCEPT ![(a_CONSTANTunde_xunde_a)] = ([(fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))) EXCEPT ![(a_CONSTANTunde_yunde_a)] = (a_CONSTANTunde_zunde_a)])]) EXCEPT ![(a_CONSTANTunde_uunde_a)] = ([(fapply (([(a_CONSTANTunde_funde_a) EXCEPT ![(a_CONSTANTunde_xunde_a)] = ([(fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))) EXCEPT ![(a_CONSTANTunde_yunde_a)] = (a_CONSTANTunde_zunde_a)])]), (a_CONSTANTunde_uunde_a))) EXCEPT ![(a_CONSTANTunde_vunde_a)] = (a_CONSTANTunde_wunde_a)])]), (a_CONSTANTunde_xunde_a))) = ([(fapply ((a_CONSTANTunde_funde_a), (a_CONSTANTunde_xunde_a))) EXCEPT ![(a_CONSTANTunde_yunde_a)] = (a_CONSTANTunde_zunde_a)])))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/function16_test.tlaps/tlapm_712523.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/function16_test.tlaps/tlapm_712523.znn.out
;; obligation #1
$hyp "a_CONSTANTunde_xunde_a_in" (TLA.in a_CONSTANTunde_xunde_a (TLA.DOMAIN a_CONSTANTunde_funde_a))
$hyp "a_CONSTANTunde_yunde_a_in" (TLA.in a_CONSTANTunde_yunde_a (TLA.DOMAIN (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a)))
$hyp "a_CONSTANTunde_uunde_a_in" (TLA.in a_CONSTANTunde_uunde_a (TLA.DOMAIN a_CONSTANTunde_funde_a))
$hyp "a_CONSTANTunde_vunde_a_in" (TLA.in a_CONSTANTunde_vunde_a (TLA.DOMAIN (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_uunde_a)))
$hyp "v'11" (-. (= a_CONSTANTunde_uunde_a
a_CONSTANTunde_xunde_a))
$goal (= (TLA.fapply (TLA.except (TLA.except a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a (TLA.except (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a) a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a)) a_CONSTANTunde_uunde_a (TLA.except (TLA.fapply (TLA.except a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a (TLA.except (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a) a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a)) a_CONSTANTunde_uunde_a) a_CONSTANTunde_vunde_a a_CONSTANTunde_wunde_a)) a_CONSTANTunde_xunde_a)
(TLA.except (TLA.fapply a_CONSTANTunde_funde_a a_CONSTANTunde_xunde_a) a_CONSTANTunde_yunde_a a_CONSTANTunde_zunde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(a_CONSTANTunde_xunde_a \\in DOMAIN(a_CONSTANTunde_funde_a))" (is "?z_ha")
 using a_CONSTANTunde_xunde_a_in by blast
 have z_He:"(a_CONSTANTunde_uunde_a~=a_CONSTANTunde_xunde_a)"
 using v'11 by blast
 assume z_Hf:"((except(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, except((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]), a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a)), a_CONSTANTunde_uunde_a, except((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, except((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]), a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))[a_CONSTANTunde_uunde_a]), a_CONSTANTunde_vunde_a, a_CONSTANTunde_wunde_a))[a_CONSTANTunde_xunde_a])~=except((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a]), a_CONSTANTunde_yunde_a, a_CONSTANTunde_zunde_a))" (is "?z_hk~=?z_hn")
 show FALSE
 proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hn))" "except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, ?z_hn)" "a_CONSTANTunde_uunde_a" "except((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, ?z_hn)[a_CONSTANTunde_uunde_a]), a_CONSTANTunde_vunde_a, a_CONSTANTunde_wunde_a)" "a_CONSTANTunde_xunde_a", OF z_Hf])
  assume z_Hy:"(a_CONSTANTunde_xunde_a \\in DOMAIN(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, ?z_hn)))" (is "?z_hy")
  assume z_Hba:"(a_CONSTANTunde_uunde_a=a_CONSTANTunde_xunde_a)"
  assume z_Hbb:"(except((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, ?z_hn)[a_CONSTANTunde_uunde_a]), a_CONSTANTunde_vunde_a, a_CONSTANTunde_wunde_a)~=?z_hn)" (is "?z_hr~=_")
  show FALSE
  by (rule notE [OF z_He z_Hba])
 next
  assume z_Hy:"(a_CONSTANTunde_xunde_a \\in DOMAIN(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, ?z_hn)))" (is "?z_hy")
  assume z_He:"(a_CONSTANTunde_uunde_a~=a_CONSTANTunde_xunde_a)"
  assume z_Hbc:"((except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, ?z_hn)[a_CONSTANTunde_xunde_a])~=?z_hn)" (is "?z_hbd~=_")
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vf. (zenon_Vf~=?z_hn))" "a_CONSTANTunde_funde_a" "a_CONSTANTunde_xunde_a" "?z_hn" "a_CONSTANTunde_xunde_a", OF z_Hbc])
   assume z_Ha:"?z_ha"
   assume z_Hbe:"(a_CONSTANTunde_xunde_a=a_CONSTANTunde_xunde_a)"
   assume z_Hbf:"(?z_hn~=?z_hn)"
   show FALSE
   by (rule zenon_noteq [OF z_Hbf])
  next
   assume z_Ha:"?z_ha"
   assume z_Hbg:"(a_CONSTANTunde_xunde_a~=a_CONSTANTunde_xunde_a)"
   assume z_Hbh:"((a_CONSTANTunde_funde_a[a_CONSTANTunde_xunde_a])~=?z_hn)" (is "?z_ho~=_")
   show FALSE
   by (rule zenon_noteq [OF z_Hbg])
  next
   assume z_Hbi:"(~?z_ha)"
   show FALSE
   by (rule notE [OF z_Hbi z_Ha])
  qed
 next
  assume z_Hbj:"(~(a_CONSTANTunde_xunde_a \\in DOMAIN(except(a_CONSTANTunde_funde_a, a_CONSTANTunde_xunde_a, ?z_hn))))" (is "~?z_hy")
  have z_Hbi: "(~?z_ha)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vv. (~(a_CONSTANTunde_xunde_a \\in zenon_Vv)))" "a_CONSTANTunde_funde_a" "a_CONSTANTunde_xunde_a" "?z_hn", OF z_Hbj])
  show FALSE
  by (rule notE [OF z_Hbi z_Ha])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
end

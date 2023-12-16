(* automatically generated -- do not edit manually *)
theory russell_test imports Constant Zenon begin
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
fixes a_CONSTANTunde_Vunde_a
assumes v'5: "(\<forall>a_CONSTANTunde_xunde_a : (((a_CONSTANTunde_xunde_a) \<in> (a_CONSTANTunde_Vunde_a))))"
shows "(((((subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a))))) \<in> (subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a))))))) \<Rightarrow> (((subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a))))) \<notin> (subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a)))))))))"(is "PROP ?ob'6")
proof -
ML_command {* writeln "*** TLAPS ENTER 6"; *}
show "PROP ?ob'6"

(* BEGIN ZENON INPUT
;; file=.tlacache/russell_test.tlaps/tlapm_5e4e22.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/russell_test.tlaps/tlapm_5e4e22.znn.out
;; obligation #6
$hyp "v'5" (A. ((a_CONSTANTunde_xunde_a) (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_Vunde_a)))
$goal (=> (TLA.in (TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a))))
(TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)))))
(-. (TLA.in (TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a))))
(TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a)))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Hb:"(~((subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))) \\in subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))))=>(~(subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))) \\in subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a))))))))" (is "~(?z_hd=>?z_hk)")
 have z_Hd: "?z_hd"
 by (rule zenon_notimply_0 [OF z_Hb])
 have z_Hk: "?z_hk"
 by (rule zenon_in_subsetof_1 [of "subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a))))" "a_CONSTANTunde_Vunde_a" "(\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))", OF z_Hd])
 show FALSE
 by (rule notE [OF z_Hk z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 6"; *} qed
lemma ob'8:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Vunde_a
assumes v'5: "(\<forall>a_CONSTANTunde_xunde_a : (((a_CONSTANTunde_xunde_a) \<in> (a_CONSTANTunde_Vunde_a))))"
shows "(((((subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a))))) \<notin> (subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a))))))) \<Rightarrow> (((subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a))))) \<in> (subsetOf((a_CONSTANTunde_Vunde_a), %a_CONSTANTunde_xunde_a. (((a_CONSTANTunde_xunde_a) \<notin> (a_CONSTANTunde_xunde_a)))))))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"

(* BEGIN ZENON INPUT
;; file=.tlacache/russell_test.tlaps/tlapm_dc7817.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/russell_test.tlaps/tlapm_dc7817.znn.out
;; obligation #8
$hyp "v'5" (A. ((a_CONSTANTunde_xunde_a) (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_Vunde_a)))
$goal (=> (-. (TLA.in (TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a))))
(TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a))))))
(TLA.in (TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a))))
(TLA.subsetOf a_CONSTANTunde_Vunde_a ((a_CONSTANTunde_xunde_a) (-. (TLA.in a_CONSTANTunde_xunde_a
a_CONSTANTunde_xunde_a))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(\\A a_CONSTANTunde_xunde_a:(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_Vunde_a))" (is "\\A x : ?z_hf(x)")
 using v'5 by blast
 assume z_Hb:"(~((~(subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))) \\in subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a))))))=>(subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))) \\in subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))))))" (is "~(?z_hh=>?z_hi)")
 have z_Hh: "?z_hh"
 by (rule zenon_notimply_0 [OF z_Hb])
 have z_Hh: "?z_hh"
 by (rule zenon_notimply_1 [OF z_Hb])
 show FALSE
 proof (rule zenon_notin_subsetof [of "subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a))))" "a_CONSTANTunde_Vunde_a" "(\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))", OF z_Hh])
  assume z_Hn:"(~(subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))) \\in a_CONSTANTunde_Vunde_a))" (is "~?z_ho")
  have z_Ho: "?z_hf(subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a)))))"
  by (rule zenon_all_0 [of "?z_hf" "subsetOf(a_CONSTANTunde_Vunde_a, (\<lambda>a_CONSTANTunde_xunde_a. (~(a_CONSTANTunde_xunde_a \\in a_CONSTANTunde_xunde_a))))", OF z_Ha])
  show FALSE
  by (rule notE [OF z_Hn z_Ho])
 next
  assume z_Hp:"(~?z_hh)"
  show FALSE
  by (rule notE [OF z_Hp z_Hh])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
end

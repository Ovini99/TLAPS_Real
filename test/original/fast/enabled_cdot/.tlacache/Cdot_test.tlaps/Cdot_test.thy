(* automatically generated -- do not edit manually *)
theory Cdot_test imports Constant Zenon begin
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
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
(* usable definition ACTION_R_ suppressed *)
(* usable definition ACTION_A_ suppressed *)
(* usable definition ACTION_B_ suppressed *)
shows "(((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (((((a_VARIABLEunde_xunde_a) = (FALSE))) & (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (TRUE)))) & ((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (TRUE))) & ((((a_VARIABLEunde_xunde_hash_primea :: c)) = (FALSE)))))) \<Leftrightarrow> ((((a_VARIABLEunde_xunde_a) = (FALSE))) & ((((a_VARIABLEunde_xunde_hash_primea :: c)) = (FALSE))))))"(is "PROP ?ob'4")
proof -
ML_command {* writeln "*** TLAPS ENTER 4"; *}
show "PROP ?ob'4"

(* BEGIN ZENON INPUT
;; file=.tlacache/Cdot_test.tlaps/tlapm_a4d884.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Cdot_test.tlaps/tlapm_a4d884.znn.out
;; obligation #4
$goal (<=> (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
F.) (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a T.))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a T.)
(= a_VARIABLEunde_xunde_hash_primea F.))))) (/\ (= a_VARIABLEunde_xunde_a F.)
(= a_VARIABLEunde_xunde_hash_primea
F.)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=FALSE)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE))&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE)&(a_VARIABLEunde_xunde_hash_primea=FALSE))))<=>((a_VARIABLEunde_xunde_a=FALSE)&(a_VARIABLEunde_xunde_hash_primea=FALSE))))" (is "~(?z_hc<=>?z_ho)")
 show FALSE
 proof (rule zenon_notequiv [OF z_Ha])
  assume z_Hp:"(~?z_hc)" (is "~(\\E x : ?z_hq(x))")
  assume z_Ho:"?z_ho" (is "?z_hf&?z_hm")
  have z_Hf: "?z_hf" (is "_=?z_hh")
  by (rule zenon_and_0 [OF z_Ho])
  have z_Hm: "?z_hm"
  by (rule zenon_and_1 [OF z_Ho])
  have z_Hr: "~?z_hq(TRUE)" (is "~(?z_hs&?z_ht)")
  by (rule zenon_notex_0 [of "?z_hq" "TRUE", OF z_Hp])
  show FALSE
  proof (rule zenon_notand [OF z_Hr])
   assume z_Hu:"(~?z_hs)" (is "~(_&?z_hv)")
   show FALSE
   proof (rule zenon_notand [OF z_Hu])
    assume z_Hw:"(a_VARIABLEunde_xunde_a~=?z_hh)"
    show FALSE
    by (rule notE [OF z_Hw z_Hf])
   next
    assume z_Hx:"(TRUE~=TRUE)" (is "?z_hk~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hx])
   qed
  next
   assume z_Hy:"(~?z_ht)" (is "~(?z_hv&_)")
   show FALSE
   proof (rule zenon_notand [OF z_Hy])
    assume z_Hx:"(TRUE~=TRUE)" (is "?z_hk~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hx])
   next
    assume z_Hz:"(a_VARIABLEunde_xunde_hash_primea~=?z_hh)"
    show FALSE
    by (rule notE [OF z_Hz z_Hm])
   qed
  qed
 next
  assume z_Hc:"?z_hc" (is "\\E x : ?z_hq(x)")
  assume z_Hba:"(~?z_ho)" (is "~(?z_hf&?z_hm)")
  have z_Hbb: "?z_hq((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hf&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE))&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE)&?z_hm))))" (is "?z_hbd&?z_hbe")
  by (rule zenon_ex_choose_0 [of "?z_hq", OF z_Hc])
  have z_Hbd: "?z_hbd" (is "_&?z_hbf")
  by (rule zenon_and_0 [OF z_Hbb])
  have z_Hbe: "?z_hbe"
  by (rule zenon_and_1 [OF z_Hbb])
  have z_Hm: "?z_hm" (is "_=?z_hh")
  by (rule zenon_and_1 [OF z_Hbe])
  have z_Hf: "?z_hf"
  by (rule zenon_and_0 [OF z_Hbd])
  show FALSE
  proof (rule zenon_notand [OF z_Hba])
   assume z_Hw:"(a_VARIABLEunde_xunde_a~=?z_hh)"
   show FALSE
   by (rule notE [OF z_Hw z_Hf])
  next
   assume z_Hz:"(a_VARIABLEunde_xunde_hash_primea~=?z_hh)"
   show FALSE
   by (rule notE [OF z_Hz z_Hm])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 4"; *} qed
lemma ob'1:
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
shows "(((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (((((a_VARIABLEunde_xunde_a) = (FALSE))) & (((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (TRUE)))) & ((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (TRUE))) & ((((a_VARIABLEunde_xunde_hash_primea :: c)) = (FALSE)))))) \<Leftrightarrow> ((((a_VARIABLEunde_xunde_a) = (FALSE))) & ((((a_VARIABLEunde_xunde_hash_primea :: c)) = (FALSE))))))"(is "PROP ?ob'1")
proof -
ML_command {* writeln "*** TLAPS ENTER 1"; *}
show "PROP ?ob'1"

(* BEGIN ZENON INPUT
;; file=.tlacache/Cdot_test.tlaps/tlapm_43e6a8.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Cdot_test.tlaps/tlapm_43e6a8.znn.out
;; obligation #1
$goal (<=> (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (= a_VARIABLEunde_xunde_a
F.) (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a T.))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a T.)
(= a_VARIABLEunde_xunde_hash_primea F.))))) (/\ (= a_VARIABLEunde_xunde_a F.)
(= a_VARIABLEunde_xunde_hash_primea
F.)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:(((a_VARIABLEunde_xunde_a=FALSE)&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE))&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE)&(a_VARIABLEunde_xunde_hash_primea=FALSE))))<=>((a_VARIABLEunde_xunde_a=FALSE)&(a_VARIABLEunde_xunde_hash_primea=FALSE))))" (is "~(?z_hc<=>?z_ho)")
 show FALSE
 proof (rule zenon_notequiv [OF z_Ha])
  assume z_Hp:"(~?z_hc)" (is "~(\\E x : ?z_hq(x))")
  assume z_Ho:"?z_ho" (is "?z_hf&?z_hm")
  have z_Hf: "?z_hf" (is "_=?z_hh")
  by (rule zenon_and_0 [OF z_Ho])
  have z_Hm: "?z_hm"
  by (rule zenon_and_1 [OF z_Ho])
  have z_Hr: "~?z_hq(TRUE)" (is "~(?z_hs&?z_ht)")
  by (rule zenon_notex_0 [of "?z_hq" "TRUE", OF z_Hp])
  show FALSE
  proof (rule zenon_notand [OF z_Hr])
   assume z_Hu:"(~?z_hs)" (is "~(_&?z_hv)")
   show FALSE
   proof (rule zenon_notand [OF z_Hu])
    assume z_Hw:"(a_VARIABLEunde_xunde_a~=?z_hh)"
    show FALSE
    by (rule notE [OF z_Hw z_Hf])
   next
    assume z_Hx:"(TRUE~=TRUE)" (is "?z_hk~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hx])
   qed
  next
   assume z_Hy:"(~?z_ht)" (is "~(?z_hv&_)")
   show FALSE
   proof (rule zenon_notand [OF z_Hy])
    assume z_Hx:"(TRUE~=TRUE)" (is "?z_hk~=_")
    show FALSE
    by (rule zenon_noteq [OF z_Hx])
   next
    assume z_Hz:"(a_VARIABLEunde_xunde_hash_primea~=?z_hh)"
    show FALSE
    by (rule notE [OF z_Hz z_Hm])
   qed
  qed
 next
  assume z_Hc:"?z_hc" (is "\\E x : ?z_hq(x)")
  assume z_Hba:"(~?z_ho)" (is "~(?z_hf&?z_hm)")
  have z_Hbb: "?z_hq((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hf&(a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE))&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=TRUE)&?z_hm))))" (is "?z_hbd&?z_hbe")
  by (rule zenon_ex_choose_0 [of "?z_hq", OF z_Hc])
  have z_Hbd: "?z_hbd" (is "_&?z_hbf")
  by (rule zenon_and_0 [OF z_Hbb])
  have z_Hbe: "?z_hbe"
  by (rule zenon_and_1 [OF z_Hbb])
  have z_Hm: "?z_hm" (is "_=?z_hh")
  by (rule zenon_and_1 [OF z_Hbe])
  have z_Hf: "?z_hf"
  by (rule zenon_and_0 [OF z_Hbd])
  show FALSE
  proof (rule zenon_notand [OF z_Hba])
   assume z_Hw:"(a_VARIABLEunde_xunde_a~=?z_hh)"
   show FALSE
   by (rule notE [OF z_Hw z_Hf])
  next
   assume z_Hz:"(a_VARIABLEunde_xunde_hash_primea~=?z_hh)"
   show FALSE
   by (rule notE [OF z_Hz z_Hm])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 1"; *} qed
lemma ob'8:
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
(* usable definition ACTION_R_ suppressed *)
(* usable definition ACTION_A_ suppressed *)
(* usable definition ACTION_B_ suppressed *)
(* usable definition ACTION_C_ suppressed *)
(* usable definition ACTION_D_ suppressed *)
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
shows "(((\<exists>a_CONSTANTunde_yhash_enabledhash_prime1unde_a : (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (((((((a_VARIABLEunde_xunde_a) = (TRUE))) \<and> (((a_VARIABLEunde_yunde_a) = (FALSE))))) & (((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (FALSE))) \<and> (((a_CONSTANTunde_yhash_enabledhash_prime1unde_a) = (TRUE)))))) & ((((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (FALSE))) \<and> (((a_CONSTANTunde_yhash_enabledhash_prime1unde_a) = (TRUE))))) & ((((((a_VARIABLEunde_xunde_hash_primea :: c)) = (TRUE))) \<and> ((((a_VARIABLEunde_yunde_hash_primea :: c)) = (TRUE))))))))) \<Leftrightarrow> ((((((a_VARIABLEunde_xunde_a) = (TRUE))) \<and> (((a_VARIABLEunde_yunde_a) = (FALSE))))) & ((((((a_VARIABLEunde_xunde_hash_primea :: c)) = (TRUE))) \<and> ((((a_VARIABLEunde_yunde_hash_primea :: c)) = (TRUE))))))))"(is "PROP ?ob'8")
proof -
ML_command {* writeln "*** TLAPS ENTER 8"; *}
show "PROP ?ob'8"

(* BEGIN ZENON INPUT
;; file=.tlacache/Cdot_test.tlaps/tlapm_4292a5.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Cdot_test.tlaps/tlapm_4292a5.znn.out
;; obligation #8
$goal (<=> (E. ((a_CONSTANTunde_yhash_enabledhash_prime1unde_a) (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (/\ (= a_VARIABLEunde_xunde_a
T.) (= a_VARIABLEunde_yunde_a F.))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a F.)
(= a_CONSTANTunde_yhash_enabledhash_prime1unde_a T.)))
(/\ (/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a F.)
(= a_CONSTANTunde_yhash_enabledhash_prime1unde_a T.))
(/\ (= a_VARIABLEunde_xunde_hash_primea T.)
(= a_VARIABLEunde_yunde_hash_primea T.))))))))
(/\ (/\ (= a_VARIABLEunde_xunde_a T.) (= a_VARIABLEunde_yunde_a F.))
(/\ (= a_VARIABLEunde_xunde_hash_primea T.)
(= a_VARIABLEunde_yunde_hash_primea
T.))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((\\E a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((((a_VARIABLEunde_xunde_a=TRUE)&(a_VARIABLEunde_yunde_a=FALSE))&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&((a_VARIABLEunde_xunde_hash_primea=TRUE)&(a_VARIABLEunde_yunde_hash_primea=TRUE))))))<=>(((a_VARIABLEunde_xunde_a=TRUE)&(a_VARIABLEunde_yunde_a=FALSE))&((a_VARIABLEunde_xunde_hash_primea=TRUE)&(a_VARIABLEunde_yunde_hash_primea=TRUE)))))" (is "~(?z_hc<=>?z_hy)")
 show FALSE
 proof (rule zenon_notequiv [OF z_Ha])
  assume z_Hz:"(~?z_hc)" (is "~(\\E x : ?z_hba(x))")
  assume z_Hy:"?z_hy" (is "?z_hg&?z_ht")
  have z_Hg: "?z_hg" (is "?z_hh&?z_hk")
  by (rule zenon_and_0 [OF z_Hy])
  have z_Ht: "?z_ht" (is "?z_hu&?z_hw")
  by (rule zenon_and_1 [OF z_Hy])
  have z_Hu: "?z_hu" (is "_=?z_hj")
  by (rule zenon_and_0 [OF z_Ht])
  have z_Hw: "?z_hw"
  by (rule zenon_and_1 [OF z_Ht])
  have z_Hh: "?z_hh"
  by (rule zenon_and_0 [OF z_Hg])
  have z_Hk: "?z_hk" (is "_=?z_hm")
  by (rule zenon_and_1 [OF z_Hg])
  have z_Hbb: "~?z_hba(?z_hj)" (is "~(\\E x : ?z_hbc(x))")
  by (rule zenon_notex_0 [of "?z_hba" "?z_hj", OF z_Hz])
  have z_Hbd: "~?z_hbc(?z_hm)" (is "~(?z_hbe&?z_hbf)")
  by (rule zenon_notex_0 [of "?z_hbc" "?z_hm", OF z_Hbb])
  show FALSE
  proof (rule zenon_notand [OF z_Hbd])
   assume z_Hbg:"(~?z_hbe)" (is "~(_&?z_hbh)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbg])
    assume z_Hbi:"(~?z_hg)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbi])
     assume z_Hbj:"(a_VARIABLEunde_xunde_a~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hbj z_Hh])
    next
     assume z_Hbk:"(a_VARIABLEunde_yunde_a~=?z_hm)"
     show FALSE
     by (rule notE [OF z_Hbk z_Hk])
    qed
   next
    assume z_Hbl:"(~?z_hbh)" (is "~(?z_hbm&?z_hbn)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbl])
     assume z_Hbo:"(?z_hm~=?z_hm)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbo])
    next
     assume z_Hbp:"(?z_hj~=?z_hj)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbp])
    qed
   qed
  next
   assume z_Hbq:"(~?z_hbf)" (is "~(?z_hbh&_)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbq])
    assume z_Hbl:"(~?z_hbh)" (is "~(?z_hbm&?z_hbn)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbl])
     assume z_Hbo:"(?z_hm~=?z_hm)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbo])
    next
     assume z_Hbp:"(?z_hj~=?z_hj)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbp])
    qed
   next
    assume z_Hbr:"(~?z_ht)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbr])
     assume z_Hbs:"(a_VARIABLEunde_xunde_hash_primea~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hbs z_Hu])
    next
     assume z_Hbt:"(a_VARIABLEunde_yunde_hash_primea~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hbt z_Hw])
    qed
   qed
  qed
 next
  assume z_Hc:"?z_hc" (is "\\E x : ?z_hba(x)")
  assume z_Hbu:"(~?z_hy)" (is "~(?z_hg&?z_ht)")
  have z_Hbv: "?z_hba((CHOOSE a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&?z_ht)))))" (is "\\E x : ?z_hbx(x)")
  by (rule zenon_ex_choose_0 [of "?z_hba", OF z_Hc])
  have z_Hby: "?z_hbx((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&((CHOOSE a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&?z_ht))))=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&((CHOOSE a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&?z_ht))))=TRUE))&?z_ht))))" (is "?z_hcf&?z_hcg")
  by (rule zenon_ex_choose_0 [of "?z_hbx", OF z_Hbv])
  have z_Hcf: "?z_hcf" (is "_&?z_hch")
  by (rule zenon_and_0 [OF z_Hby])
  have z_Hcg: "?z_hcg"
  by (rule zenon_and_1 [OF z_Hby])
  have z_Ht: "?z_ht" (is "?z_hu&?z_hw")
  by (rule zenon_and_1 [OF z_Hcg])
  have z_Hu: "?z_hu" (is "_=?z_hj")
  by (rule zenon_and_0 [OF z_Ht])
  have z_Hw: "?z_hw"
  by (rule zenon_and_1 [OF z_Ht])
  have z_Hg: "?z_hg" (is "?z_hh&?z_hk")
  by (rule zenon_and_0 [OF z_Hcf])
  have z_Hh: "?z_hh"
  by (rule zenon_and_0 [OF z_Hg])
  have z_Hk: "?z_hk" (is "_=?z_hm")
  by (rule zenon_and_1 [OF z_Hg])
  show FALSE
  proof (rule zenon_notand [OF z_Hbu])
   assume z_Hbi:"(~?z_hg)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbi])
    assume z_Hbj:"(a_VARIABLEunde_xunde_a~=?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbj z_Hh])
   next
    assume z_Hbk:"(a_VARIABLEunde_yunde_a~=?z_hm)"
    show FALSE
    by (rule notE [OF z_Hbk z_Hk])
   qed
  next
   assume z_Hbr:"(~?z_ht)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbr])
    assume z_Hbs:"(a_VARIABLEunde_xunde_hash_primea~=?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbs z_Hu])
   next
    assume z_Hbt:"(a_VARIABLEunde_yunde_hash_primea~=?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbt z_Hw])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 8"; *} qed
lemma ob'11:
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
(* usable definition ACTION_R_ suppressed *)
(* usable definition ACTION_A_ suppressed *)
(* usable definition ACTION_B_ suppressed *)
(* usable definition ACTION_C_ suppressed *)
(* usable definition ACTION_D_ suppressed *)
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
(* usable definition ACTION_A2_ suppressed *)
(* usable definition ACTION_B2_ suppressed *)
shows "(((\<exists>a_CONSTANTunde_yhash_enabledhash_prime1unde_a : (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (((((((a_VARIABLEunde_xunde_a) = (TRUE))) \<and> (((a_VARIABLEunde_yunde_a) = (FALSE))))) & (((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (FALSE))) \<and> (((a_CONSTANTunde_yhash_enabledhash_prime1unde_a) = (TRUE)))))) & ((((((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) = (FALSE))) \<and> (((a_CONSTANTunde_yhash_enabledhash_prime1unde_a) = (TRUE))))) & ((((((a_VARIABLEunde_xunde_hash_primea :: c)) = (TRUE))) \<and> ((((a_VARIABLEunde_yunde_hash_primea :: c)) = (TRUE))))))))) \<Leftrightarrow> ((((((a_VARIABLEunde_xunde_a) = (TRUE))) \<and> (((a_VARIABLEunde_yunde_a) = (FALSE))))) & ((((((a_VARIABLEunde_xunde_hash_primea :: c)) = (TRUE))) \<and> ((((a_VARIABLEunde_yunde_hash_primea :: c)) = (TRUE))))))))"(is "PROP ?ob'11")
proof -
ML_command {* writeln "*** TLAPS ENTER 11"; *}
show "PROP ?ob'11"

(* BEGIN ZENON INPUT
;; file=.tlacache/Cdot_test.tlaps/tlapm_172d3d.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Cdot_test.tlaps/tlapm_172d3d.znn.out
;; obligation #11
$goal (<=> (E. ((a_CONSTANTunde_yhash_enabledhash_prime1unde_a) (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) (/\ (/\ (/\ (= a_VARIABLEunde_xunde_a
T.) (= a_VARIABLEunde_yunde_a F.))
(/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a F.)
(= a_CONSTANTunde_yhash_enabledhash_prime1unde_a T.)))
(/\ (/\ (= a_CONSTANTunde_xhash_enabledhash_prime1unde_a F.)
(= a_CONSTANTunde_yhash_enabledhash_prime1unde_a T.))
(/\ (= a_VARIABLEunde_xunde_hash_primea T.)
(= a_VARIABLEunde_yunde_hash_primea T.))))))))
(/\ (/\ (= a_VARIABLEunde_xunde_a T.) (= a_VARIABLEunde_yunde_a F.))
(/\ (= a_VARIABLEunde_xunde_hash_primea T.)
(= a_VARIABLEunde_yunde_hash_primea
T.))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((\\E a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((((a_VARIABLEunde_xunde_a=TRUE)&(a_VARIABLEunde_yunde_a=FALSE))&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&((a_VARIABLEunde_xunde_hash_primea=TRUE)&(a_VARIABLEunde_yunde_hash_primea=TRUE))))))<=>(((a_VARIABLEunde_xunde_a=TRUE)&(a_VARIABLEunde_yunde_a=FALSE))&((a_VARIABLEunde_xunde_hash_primea=TRUE)&(a_VARIABLEunde_yunde_hash_primea=TRUE)))))" (is "~(?z_hc<=>?z_hy)")
 show FALSE
 proof (rule zenon_notequiv [OF z_Ha])
  assume z_Hz:"(~?z_hc)" (is "~(\\E x : ?z_hba(x))")
  assume z_Hy:"?z_hy" (is "?z_hg&?z_ht")
  have z_Hg: "?z_hg" (is "?z_hh&?z_hk")
  by (rule zenon_and_0 [OF z_Hy])
  have z_Ht: "?z_ht" (is "?z_hu&?z_hw")
  by (rule zenon_and_1 [OF z_Hy])
  have z_Hu: "?z_hu" (is "_=?z_hj")
  by (rule zenon_and_0 [OF z_Ht])
  have z_Hw: "?z_hw"
  by (rule zenon_and_1 [OF z_Ht])
  have z_Hh: "?z_hh"
  by (rule zenon_and_0 [OF z_Hg])
  have z_Hk: "?z_hk" (is "_=?z_hm")
  by (rule zenon_and_1 [OF z_Hg])
  have z_Hbb: "~?z_hba(?z_hj)" (is "~(\\E x : ?z_hbc(x))")
  by (rule zenon_notex_0 [of "?z_hba" "?z_hj", OF z_Hz])
  have z_Hbd: "~?z_hbc(?z_hm)" (is "~(?z_hbe&?z_hbf)")
  by (rule zenon_notex_0 [of "?z_hbc" "?z_hm", OF z_Hbb])
  show FALSE
  proof (rule zenon_notand [OF z_Hbd])
   assume z_Hbg:"(~?z_hbe)" (is "~(_&?z_hbh)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbg])
    assume z_Hbi:"(~?z_hg)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbi])
     assume z_Hbj:"(a_VARIABLEunde_xunde_a~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hbj z_Hh])
    next
     assume z_Hbk:"(a_VARIABLEunde_yunde_a~=?z_hm)"
     show FALSE
     by (rule notE [OF z_Hbk z_Hk])
    qed
   next
    assume z_Hbl:"(~?z_hbh)" (is "~(?z_hbm&?z_hbn)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbl])
     assume z_Hbo:"(?z_hm~=?z_hm)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbo])
    next
     assume z_Hbp:"(?z_hj~=?z_hj)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbp])
    qed
   qed
  next
   assume z_Hbq:"(~?z_hbf)" (is "~(?z_hbh&_)")
   show FALSE
   proof (rule zenon_notand [OF z_Hbq])
    assume z_Hbl:"(~?z_hbh)" (is "~(?z_hbm&?z_hbn)")
    show FALSE
    proof (rule zenon_notand [OF z_Hbl])
     assume z_Hbo:"(?z_hm~=?z_hm)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbo])
    next
     assume z_Hbp:"(?z_hj~=?z_hj)"
     show FALSE
     by (rule zenon_noteq [OF z_Hbp])
    qed
   next
    assume z_Hbr:"(~?z_ht)"
    show FALSE
    proof (rule zenon_notand [OF z_Hbr])
     assume z_Hbs:"(a_VARIABLEunde_xunde_hash_primea~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hbs z_Hu])
    next
     assume z_Hbt:"(a_VARIABLEunde_yunde_hash_primea~=?z_hj)"
     show FALSE
     by (rule notE [OF z_Hbt z_Hw])
    qed
   qed
  qed
 next
  assume z_Hc:"?z_hc" (is "\\E x : ?z_hba(x)")
  assume z_Hbu:"(~?z_hy)" (is "~(?z_hg&?z_ht)")
  have z_Hbv: "?z_hba((CHOOSE a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&?z_ht)))))" (is "\\E x : ?z_hbx(x)")
  by (rule zenon_ex_choose_0 [of "?z_hba", OF z_Hc])
  have z_Hby: "?z_hbx((CHOOSE a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&((CHOOSE a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&?z_ht))))=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&((CHOOSE a_CONSTANTunde_yhash_enabledhash_prime1unde_a:(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:((?z_hg&((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE)))&(((a_CONSTANTunde_xhash_enabledhash_prime1unde_a=FALSE)&(a_CONSTANTunde_yhash_enabledhash_prime1unde_a=TRUE))&?z_ht))))=TRUE))&?z_ht))))" (is "?z_hcf&?z_hcg")
  by (rule zenon_ex_choose_0 [of "?z_hbx", OF z_Hbv])
  have z_Hcf: "?z_hcf" (is "_&?z_hch")
  by (rule zenon_and_0 [OF z_Hby])
  have z_Hcg: "?z_hcg"
  by (rule zenon_and_1 [OF z_Hby])
  have z_Ht: "?z_ht" (is "?z_hu&?z_hw")
  by (rule zenon_and_1 [OF z_Hcg])
  have z_Hu: "?z_hu" (is "_=?z_hj")
  by (rule zenon_and_0 [OF z_Ht])
  have z_Hw: "?z_hw"
  by (rule zenon_and_1 [OF z_Ht])
  have z_Hg: "?z_hg" (is "?z_hh&?z_hk")
  by (rule zenon_and_0 [OF z_Hcf])
  have z_Hh: "?z_hh"
  by (rule zenon_and_0 [OF z_Hg])
  have z_Hk: "?z_hk" (is "_=?z_hm")
  by (rule zenon_and_1 [OF z_Hg])
  show FALSE
  proof (rule zenon_notand [OF z_Hbu])
   assume z_Hbi:"(~?z_hg)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbi])
    assume z_Hbj:"(a_VARIABLEunde_xunde_a~=?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbj z_Hh])
   next
    assume z_Hbk:"(a_VARIABLEunde_yunde_a~=?z_hm)"
    show FALSE
    by (rule notE [OF z_Hbk z_Hk])
   qed
  next
   assume z_Hbr:"(~?z_ht)"
   show FALSE
   proof (rule zenon_notand [OF z_Hbr])
    assume z_Hbs:"(a_VARIABLEunde_xunde_hash_primea~=?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbs z_Hu])
   next
    assume z_Hbt:"(a_VARIABLEunde_yunde_hash_primea~=?z_hj)"
    show FALSE
    by (rule notE [OF z_Hbt z_Hw])
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 11"; *} qed
end

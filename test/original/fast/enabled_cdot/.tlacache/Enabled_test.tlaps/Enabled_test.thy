(* automatically generated -- do not edit manually *)
theory Enabled_test imports Constant Zenon begin
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

lemma ob'5:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
(* usable definition ACTION_P_ suppressed *)
(* usable definition STATE_Q_ suppressed *)
shows "(\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_CONSTANTunde_xhash_enabledhash_prime1unde_a))"(is "PROP ?ob'5")
proof -
ML_command {* writeln "*** TLAPS ENTER 5"; *}
show "PROP ?ob'5"

(* BEGIN ZENON INPUT
;; file=.tlacache/Enabled_test.tlaps/tlapm_abe0b1.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Enabled_test.tlaps/tlapm_abe0b1.znn.out
;; obligation #5
$goal (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_CONSTANTunde_xhash_enabledhash_prime1unde_a))" (is "~(\\E x : ?z_hd(x))")
 have z_He: "~?z_hd(TRUE)" (is "~?z_hf")
 by (rule zenon_notex_0 [of "?z_hd" "?z_hf", OF z_Ha])
 show FALSE
 by (rule zenon_nottrue [OF z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 5"; *} qed
lemma ob'3:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
(* usable definition ACTION_P_ suppressed *)
(* usable definition STATE_Q_ suppressed *)
(* usable definition STATE_R_ suppressed *)
shows "(\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_CONSTANTunde_xhash_enabledhash_prime1unde_a))"(is "PROP ?ob'3")
proof -
ML_command {* writeln "*** TLAPS ENTER 3"; *}
show "PROP ?ob'3"

(* BEGIN ZENON INPUT
;; file=.tlacache/Enabled_test.tlaps/tlapm_5cd94a.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Enabled_test.tlaps/tlapm_5cd94a.znn.out
;; obligation #3
$goal (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_CONSTANTunde_xhash_enabledhash_prime1unde_a))" (is "~(\\E x : ?z_hd(x))")
 have z_He: "~?z_hd(TRUE)" (is "~?z_hf")
 by (rule zenon_notex_0 [of "?z_hd" "?z_hf", OF z_Ha])
 show FALSE
 by (rule zenon_nottrue [OF z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 3"; *} qed
lemma ob'15:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
(* usable definition STATE_Q_ suppressed *)
(* usable definition STATE_R_ suppressed *)
shows "(((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_CONSTANTunde_xhash_enabledhash_prime1unde_a)) \<or> (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_STATEunde_Qunde_a))))"(is "PROP ?ob'15")
proof -
ML_command {* writeln "*** TLAPS ENTER 15"; *}
show "PROP ?ob'15"

(* BEGIN ZENON INPUT
;; file=.tlacache/Enabled_test.tlaps/tlapm_4053d1.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Enabled_test.tlaps/tlapm_4053d1.znn.out
;; obligation #15
$goal (\/ (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_STATEunde_Qunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_CONSTANTunde_xhash_enabledhash_prime1unde_a)|(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_STATEunde_Qunde_a)))" (is "~(?z_hc|?z_he)")
 have z_Hg: "(~?z_hc)" (is "~(\\E x : ?z_hh(x))")
 by (rule zenon_notor_0 [OF z_Ha])
 have z_Hi: "~?z_hh(TRUE)" (is "~?z_hj")
 by (rule zenon_notex_0 [of "?z_hh" "?z_hj", OF z_Hg])
 show FALSE
 by (rule zenon_nottrue [OF z_Hi])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 15"; *} qed
lemma ob'12:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
(* usable definition ACTION_P_ suppressed *)
(* usable definition STATE_Q_ suppressed *)
(* usable definition STATE_R_ suppressed *)
shows "(\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_CONSTANTunde_xhash_enabledhash_prime1unde_a))"(is "PROP ?ob'12")
proof -
ML_command {* writeln "*** TLAPS ENTER 12"; *}
show "PROP ?ob'12"

(* BEGIN ZENON INPUT
;; file=.tlacache/Enabled_test.tlaps/tlapm_fd9b4d.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Enabled_test.tlaps/tlapm_fd9b4d.znn.out
;; obligation #12
$goal (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_CONSTANTunde_xhash_enabledhash_prime1unde_a))" (is "~(\\E x : ?z_hd(x))")
 have z_He: "~?z_hd(TRUE)" (is "~?z_hf")
 by (rule zenon_notex_0 [of "?z_hd" "?z_hf", OF z_Ha])
 show FALSE
 by (rule zenon_nottrue [OF z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 12"; *} qed
lemma ob'7:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
(* usable definition ACTION_P_ suppressed *)
(* usable definition STATE_Q_ suppressed *)
(* usable definition STATE_R_ suppressed *)
shows "(\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_CONSTANTunde_xhash_enabledhash_prime1unde_a))"(is "PROP ?ob'7")
proof -
ML_command {* writeln "*** TLAPS ENTER 7"; *}
show "PROP ?ob'7"

(* BEGIN ZENON INPUT
;; file=.tlacache/Enabled_test.tlaps/tlapm_5ad24e.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Enabled_test.tlaps/tlapm_5ad24e.znn.out
;; obligation #7
$goal (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_CONSTANTunde_xhash_enabledhash_prime1unde_a))" (is "~(\\E x : ?z_hd(x))")
 have z_He: "~?z_hd(TRUE)" (is "~?z_hf")
 by (rule zenon_notex_0 [of "?z_hd" "?z_hf", OF z_Ha])
 show FALSE
 by (rule zenon_nottrue [OF z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 7"; *} qed
lemma ob'10:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
(* usable definition STATE_Q_ suppressed *)
(* usable definition STATE_R_ suppressed *)
shows "(\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_CONSTANTunde_xhash_enabledhash_prime1unde_a))"(is "PROP ?ob'10")
proof -
ML_command {* writeln "*** TLAPS ENTER 10"; *}
show "PROP ?ob'10"

(* BEGIN ZENON INPUT
;; file=.tlacache/Enabled_test.tlaps/tlapm_171647.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Enabled_test.tlaps/tlapm_171647.znn.out
;; obligation #10
$goal (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_CONSTANTunde_xhash_enabledhash_prime1unde_a))" (is "~(\\E x : ?z_hd(x))")
 have z_He: "~?z_hd(TRUE)" (is "~?z_hf")
 by (rule zenon_notex_0 [of "?z_hd" "?z_hf", OF z_Ha])
 show FALSE
 by (rule zenon_nottrue [OF z_He])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 10"; *} qed
lemma ob'17:
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
fixes a_VARIABLEunde_yunde_a a_VARIABLEunde_yunde_a'
fixes a_VARIABLEunde_zunde_a a_VARIABLEunde_zunde_a'
(* usable definition ACTION_P_ suppressed *)
(* usable definition STATE_Q_ suppressed *)
(* usable definition STATE_R_ suppressed *)
shows "(((\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_CONSTANTunde_xhash_enabledhash_prime1unde_a)) \<or> (\<exists>a_CONSTANTunde_xhash_enabledhash_prime1unde_a : (a_STATEunde_Qunde_a))))"(is "PROP ?ob'17")
proof -
ML_command {* writeln "*** TLAPS ENTER 17"; *}
show "PROP ?ob'17"

(* BEGIN ZENON INPUT
;; file=.tlacache/Enabled_test.tlaps/tlapm_d8f107.znn; PATH='/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main/test/lib/tlaps/bin/:/home/ovini/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/snap/bin:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/tlapm-main:/home/ovini/Downloads/tlapm_real_altered/tlapm-main/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >.tlacache/Enabled_test.tlaps/tlapm_d8f107.znn.out
;; obligation #17
$goal (\/ (E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_CONSTANTunde_xhash_enabledhash_prime1unde_a))
(E. ((a_CONSTANTunde_xhash_enabledhash_prime1unde_a) a_STATEunde_Qunde_a)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 assume z_Ha:"(~((\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_CONSTANTunde_xhash_enabledhash_prime1unde_a)|(\\E a_CONSTANTunde_xhash_enabledhash_prime1unde_a:a_STATEunde_Qunde_a)))" (is "~(?z_hc|?z_he)")
 have z_Hg: "(~?z_hc)" (is "~(\\E x : ?z_hh(x))")
 by (rule zenon_notor_0 [OF z_Ha])
 have z_Hi: "~?z_hh(TRUE)" (is "~?z_hj")
 by (rule zenon_notex_0 [of "?z_hh" "?z_hj", OF z_Hg])
 show FALSE
 by (rule zenon_nottrue [OF z_Hi])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 17"; *} qed
end

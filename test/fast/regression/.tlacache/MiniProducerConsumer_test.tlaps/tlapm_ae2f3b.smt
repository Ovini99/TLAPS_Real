;; Proof obligation:
;;ASSUME NEW VARIABLE VARIABLE_in_,
;;        NEW VARIABLE VARIABLE_out_,
;;        NEW VARIABLE VARIABLE_buf_,
;;        NEW CONSTANT CONSTANT_N_,
;;        NEW CONSTANT CONSTANT_Msg_,
;;        NEW CONSTANT CONSTANT_Input_,
;;        NEW CONSTANT CONSTANT_S_,
;;        NEW CONSTANT CONSTANT_s_ \in Seq(CONSTANT_S_),
;;        NEW CONSTANT CONSTANT_t_ \in Seq(CONSTANT_S_),
;;        NEW CONSTANT CONSTANT_u_ \in [Nat \ {0} -> CONSTANT_S_]
;; PROVE  [CONSTANT_i_ \in Nat \ {0} |->
;;           IF CONSTANT_i_ =< Len(CONSTANT_s_ \o CONSTANT_t_)
;;             THEN (CONSTANT_s_ \o CONSTANT_t_)[CONSTANT_i_]
;;             ELSE CONSTANT_u_[CONSTANT_i_ - Len(CONSTANT_s_ \o CONSTANT_t_)]]
;;        = [CONSTANT_i_ \in Nat \ {0} |->
;;             IF CONSTANT_i_ =< Len(CONSTANT_s_)
;;               THEN CONSTANT_s_[CONSTANT_i_]
;;               ELSE [CONSTANT_i__1 \in Nat \ {0} |->
;;                       IF CONSTANT_i__1 =< Len(CONSTANT_t_)
;;                         THEN CONSTANT_t_[CONSTANT_i__1]
;;                         ELSE CONSTANT_u_[CONSTANT_i__1 - Len(CONSTANT_t_)]][CONSTANT_i_
;;                                                                     - Len
;;                                                                     (CONSTANT_s_)]]
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #1
;;   generated from file "./MiniProducerConsumer_test.tla", line 19, characters 2-3

(set-logic NRA)
(declare-sort u 0)
;; Standard TLA+ operators
(declare-fun int2u (Int) u)
(declare-fun real2u (Real) u)
(declare-fun u2int (u) Int)
(declare-fun u2real (u) Real)
(declare-fun tla__Int () u)
(declare-fun tla__plus (u u) u)
(declare-fun tla__minus (u u) u)
(declare-fun tla__le (u u) Bool)
(declare-fun tla__Range (u u) u)
(declare-fun tla__in (u u) Bool)
(declare-fun tla__emptyset () u)
(declare-fun tla__isAFcn (u) Bool)
(declare-fun tla__DOMAIN (u) u)
(declare-fun tla__fcnapp (u u) u)
(declare-fun tla__unspec (u u) u)
(declare-fun tla__Seq (u) u)
(declare-fun tla__Len (u) Int)

;; Terms, predicates and strings
(declare-fun a_CONSTANTunde_Sunde_a () u)
(declare-fun a_CONSTANTunde_sunde_a () u)
(declare-fun a_CONSTANTunde_tunde_a () u)
(declare-fun a_CONSTANTunde_uunde_a () u)
(declare-fun a_aunde_unde_4a () u)
(declare-fun a_aunde_unde_5a () u)
(declare-fun a_newvarunde_unde_2a () u)

(assert
  (forall ((X_9 Int)) (! (= (u2int (int2u X_9)) X_9) :pattern ((int2u X_9)))))
(assert
  (forall ((X_9 Real))
  (! (= (u2real (real2u X_9)) X_9) :pattern ((real2u X_9)))))
(assert
  (forall ((X_9 u))
  (! (= (tla__in X_9 tla__Int) (exists ((N_8 Int)) (= X_9 (int2u N_8)))) :pattern ((tla__in X_9 tla__Int)))))
(assert
  (forall ((M_7 Real) (N_8 Real))
  (! (= (tla__plus (real2u M_7) (real2u N_8)) (real2u (+ M_7 N_8))) :pattern ((tla__plus (real2u M_7) (real2u N_8))))))
(assert
  (forall ((M_7 Real) (N_8 Real))
  (! (= (tla__minus (real2u M_7) (real2u N_8)) (real2u (- M_7 N_8))) :pattern ((tla__minus (real2u M_7) (real2u N_8))))))
(assert
  (forall ((M_7 Real) (N_8 Real))
  (! (= (tla__le (real2u M_7) (real2u N_8)) (<= M_7 N_8)) :pattern ((tla__le (real2u M_7) (real2u N_8))))))
(assert
  (forall ((M_7 Real) (N_8 Real) (Z_11 u))
  (=
  (tla__in Z_11 (tla__Range (real2u M_7) (real2u N_8)))
  (exists ((X_9 Real)) (and (= Z_11 (real2u X_9)) (<= M_7 X_9) (<= X_9 N_8))))))
(assert
  (forall ((M_7 Real) (N_8 Real) (X_9 Real) (Y_10 Real))
  (=>
  (and
  (or (<= M_7 N_8) (<= X_9 Y_10))
  (=
  (tla__Range (real2u M_7) (real2u N_8))
  (tla__Range (real2u X_9) (real2u Y_10))))
  (and (= M_7 X_9) (= N_8 Y_10)))))
(assert
  (forall ((M_7 Real) (N_8 Real))
  (= (= (tla__Range (real2u M_7) (real2u N_8)) tla__emptyset) (< N_8 M_7))))
(assert
  (forall ((S_12 u) (T_13 u))
  (=>
  (forall ((X_9 u)) (= (tla__in X_9 S_12) (tla__in X_9 T_13))) (= S_12 T_13))))
(assert
  (forall ((X_9 u))
  (! (= (tla__in X_9 tla__emptyset) false) :pattern ((tla__in X_9 tla__emptyset)))))
(assert
  (forall ((F_15 u) (G_16 u))
  (=>
  (and
  (tla__isAFcn F_15) (tla__isAFcn G_16)
  (forall ((X_9 u))
  (= (tla__in X_9 (tla__DOMAIN F_15)) (tla__in X_9 (tla__DOMAIN G_16)))))
  (= (tla__DOMAIN F_15) (tla__DOMAIN G_16)))))
(assert
  (forall ((F_15 u) (G_16 u))
  (=>
  (and
  (tla__isAFcn F_15) (tla__isAFcn G_16)
  (= (tla__DOMAIN F_15) (tla__DOMAIN G_16))
  (forall ((X_9 u))
  (=>
  (tla__in X_9 (tla__DOMAIN G_16))
  (= (tla__fcnapp F_15 X_9) (tla__fcnapp G_16 X_9)))))
  (= F_15 G_16))))
(assert
  (forall ((S_12 u) (T_13 u))
  (=
  (tla__in S_12 (tla__Seq T_13))
  (and
  (<= 0 (tla__Len S_12)) (tla__isAFcn S_12)
  (= (tla__DOMAIN S_12) (tla__Range (int2u 1) (int2u (tla__Len S_12))))
  (forall ((I_14 Int))
  (=>
  (and (<= 1 I_14) (<= I_14 (tla__Len S_12)))
  (tla__in (tla__fcnapp S_12 (int2u I_14)) T_13)))))))
(assert
  (forall ((S_12 u) (N_8 Int))
  (=>
  (<= 0 N_8)
  (=
  (= (tla__DOMAIN S_12) (tla__Range (int2u 1) (int2u N_8)))
  (= (tla__Len S_12) N_8)))))
(assert (forall ((S_12 u)) (<= 0 (tla__Len S_12))))

;; Theorem to be Proved
(assert (not
  (forall ((a_v3a Int) (a_aunde_unde_4a u))
    (=>
      (and
        (tla__isAFcn a_aunde_unde_4a)
        (= (tla__DOMAIN a_aunde_unde_4a) a_aunde_unde_5a)
        (forall ((a_CONSTANTunde_iunde_unde_1a u))
          (=>
            (and
              (tla__in a_CONSTANTunde_iunde_unde_1a tla__Int)
              (tla__le (int2u 0) a_CONSTANTunde_iunde_unde_1a)
              (not (= a_CONSTANTunde_iunde_unde_1a (int2u 0))))
            (ite
              (tla__le
                a_CONSTANTunde_iunde_unde_1a
                (int2u (tla__Len a_CONSTANTunde_tunde_a)))
              (ite
                (tla__in
                  a_CONSTANTunde_iunde_unde_1a
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (=
                  (tla__fcnapp a_aunde_unde_4a a_CONSTANTunde_iunde_unde_1a)
                  (tla__fcnapp
                    a_CONSTANTunde_tunde_a a_CONSTANTunde_iunde_unde_1a))
                (=
                  (tla__fcnapp a_aunde_unde_4a a_CONSTANTunde_iunde_unde_1a)
                  (tla__unspec
                    a_CONSTANTunde_tunde_a a_CONSTANTunde_iunde_unde_1a)))
              (ite
                (and
                  (tla__in
                    (tla__minus
                      a_CONSTANTunde_iunde_unde_1a
                      (int2u (tla__Len a_CONSTANTunde_tunde_a))) tla__Int)
                  (tla__le
                    (int2u 0)
                    (tla__minus
                      a_CONSTANTunde_iunde_unde_1a
                      (int2u (tla__Len a_CONSTANTunde_tunde_a))))
                  (not
                    (=
                      (tla__minus
                        a_CONSTANTunde_iunde_unde_1a
                        (int2u (tla__Len a_CONSTANTunde_tunde_a))) (int2u 0))))
                (=
                  (tla__fcnapp a_aunde_unde_4a a_CONSTANTunde_iunde_unde_1a)
                  (tla__fcnapp
                    a_CONSTANTunde_uunde_a
                    (tla__minus
                      a_CONSTANTunde_iunde_unde_1a
                      (int2u (tla__Len a_CONSTANTunde_tunde_a)))))
                (=
                  (tla__fcnapp a_aunde_unde_4a a_CONSTANTunde_iunde_unde_1a)
                  (tla__unspec
                    a_CONSTANTunde_uunde_a
                    (tla__minus
                      a_CONSTANTunde_iunde_unde_1a
                      (int2u (tla__Len a_CONSTANTunde_tunde_a)))))))))
        (<= 0 a_v3a) (not (= a_v3a 0)))
      (=
        (ite
          (tla__le
            (int2u a_v3a)
            (int2u
              (tla__plus
                (tla__Len a_CONSTANTunde_sunde_a)
                (tla__Len a_CONSTANTunde_tunde_a))))
          (ite
            (and
              (<= 1 a_v3a)
              (tla__le
                (int2u a_v3a) (int2u (tla__Len a_CONSTANTunde_sunde_a))))
            (ite
              (tla__in (int2u a_v3a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp a_CONSTANTunde_sunde_a (int2u a_v3a))
              (tla__unspec a_CONSTANTunde_sunde_a (int2u a_v3a)))
            (ite
              (tla__in
                (int2u a_v3a)
                (tla__Range
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_sunde_a)
                      (tla__Len a_CONSTANTunde_tunde_a)))))
              (ite
                (tla__in
                  (int2u (- a_v3a (tla__Len a_CONSTANTunde_sunde_a)))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v3a (tla__Len a_CONSTANTunde_sunde_a))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v3a (tla__Len a_CONSTANTunde_sunde_a)))))
              a_newvarunde_unde_2a))
          (ite
            (and
              (tla__le
                (int2u
                  (tla__plus
                    (tla__Len a_CONSTANTunde_tunde_a)
                    (tla__Len a_CONSTANTunde_sunde_a))) (int2u a_v3a))
              (not
                (=
                  (int2u a_v3a)
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_tunde_a)
                      (tla__Len a_CONSTANTunde_sunde_a))))))
            (tla__fcnapp
              a_CONSTANTunde_uunde_a
              (int2u
                (-
                  (- a_v3a (tla__Len a_CONSTANTunde_sunde_a))
                  (tla__Len a_CONSTANTunde_tunde_a))))
            (tla__unspec
              a_CONSTANTunde_uunde_a
              (int2u
                (-
                  (- a_v3a (tla__Len a_CONSTANTunde_sunde_a))
                  (tla__Len a_CONSTANTunde_tunde_a))))))
        (ite
          (tla__le (int2u a_v3a) (int2u (tla__Len a_CONSTANTunde_sunde_a)))
          (ite
            (tla__in (int2u a_v3a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
            (tla__fcnapp a_CONSTANTunde_sunde_a (int2u a_v3a))
            (tla__unspec a_CONSTANTunde_sunde_a (int2u a_v3a)))
          (ite
            (and
              (tla__le
                (int2u (tla__Len a_CONSTANTunde_sunde_a)) (int2u a_v3a))
              (not
                (and
                  (<= 0 a_v3a)
                  (=
                    (tla__DOMAIN a_CONSTANTunde_sunde_a)
                    (tla__Range (int2u 1) (int2u a_v3a))))))
            (ite
              (tla__le
                (int2u a_v3a)
                (int2u
                  (tla__plus
                    (tla__Len a_CONSTANTunde_tunde_a)
                    (tla__Len a_CONSTANTunde_sunde_a))))
              (ite
                (tla__in
                  (int2u (- a_v3a (tla__Len a_CONSTANTunde_sunde_a)))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v3a (tla__Len a_CONSTANTunde_sunde_a))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v3a (tla__Len a_CONSTANTunde_sunde_a)))))
              (ite
                (and
                  (tla__le
                    (int2u
                      (tla__plus
                        (tla__Len a_CONSTANTunde_tunde_a)
                        (tla__Len a_CONSTANTunde_sunde_a))) (int2u a_v3a))
                  (not
                    (=
                      (int2u a_v3a)
                      (int2u
                        (tla__plus
                          (tla__Len a_CONSTANTunde_tunde_a)
                          (tla__Len a_CONSTANTunde_sunde_a))))))
                (tla__fcnapp
                  a_CONSTANTunde_uunde_a
                  (int2u
                    (-
                      (- a_v3a (tla__Len a_CONSTANTunde_sunde_a))
                      (tla__Len a_CONSTANTunde_tunde_a))))
                (tla__unspec
                  a_CONSTANTunde_uunde_a
                  (int2u
                    (-
                      (- a_v3a (tla__Len a_CONSTANTunde_sunde_a))
                      (tla__Len a_CONSTANTunde_tunde_a))))))
            (tla__unspec
              a_aunde_unde_4a
              (int2u (- a_v3a (tla__Len a_CONSTANTunde_sunde_a)))))))))))
(assert
  (forall ((a_v6a u))
    (! (=
         (tla__in a_v6a a_aunde_unde_5a)
         (and
           (tla__in a_v6a tla__Int) (tla__le (int2u 0) a_v6a)
           (not (= a_v6a (int2u 0))))) :pattern ((tla__in
                                                   a_v6a a_aunde_unde_5a)))))
(assert (tla__in a_CONSTANTunde_sunde_a (tla__Seq a_CONSTANTunde_Sunde_a)))
(assert (tla__in a_CONSTANTunde_tunde_a (tla__Seq a_CONSTANTunde_Sunde_a)))
(assert (tla__isAFcn a_CONSTANTunde_uunde_a))
(assert (= (tla__DOMAIN a_CONSTANTunde_uunde_a) a_aunde_unde_5a))
(assert
  (forall ((a_v1a Int))
    (=>
      (and (<= 0 a_v1a) (not (= a_v1a 0)))
      (tla__in
        (tla__fcnapp a_CONSTANTunde_uunde_a (int2u a_v1a))
        a_CONSTANTunde_Sunde_a))))

(check-sat)
(exit)

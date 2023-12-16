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
;;        Len(CONSTANT_t_) # 0 
;; PROVE  CONSTANT_s_ \o CONSTANT_t_
;;        = Append(CONSTANT_s_, Head(CONSTANT_t_)) \o Tail(CONSTANT_t_)
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #2
;;   generated from file "./MiniProducerConsumer_test.tla", line 25, characters 1-7

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
(declare-fun tla__lt (u u) Bool)
(declare-fun tla__le (u u) Bool)
(declare-fun tla__Range (u u) u)
(declare-fun tla__in (u u) Bool)
(declare-fun tla__emptyset () u)
(declare-fun tla__isAFcn (u) Bool)
(declare-fun tla__DOMAIN (u) u)
(declare-fun tla__fcnapp (u u) u)
(declare-fun tla__unspec (u u) u)
(declare-fun tla__tuple0 () u)
(declare-fun tla__Seq (u) u)
(declare-fun tla__Len (u) Int)

;; Terms, predicates and strings
(declare-fun a_CONSTANTunde_Sunde_a () u)
(declare-fun a_CONSTANTunde_sunde_a () u)
(declare-fun a_CONSTANTunde_tunde_a () u)
(declare-fun a_newvarunde_unde_10a () u)
(declare-fun a_newvarunde_unde_11a () u)
(declare-fun a_newvarunde_unde_13a () u)
(declare-fun a_newvarunde_unde_15a () u)
(declare-fun a_newvarunde_unde_16a () u)
(declare-fun a_newvarunde_unde_17a () u)
(declare-fun a_newvarunde_unde_18a () u)
(declare-fun a_newvarunde_unde_7a () u)
(declare-fun a_newvarunde_unde_8a () u)
(declare-fun a_newvarunde_unde_9a () u)

(assert
  (forall ((X_21 Int))
  (! (= (u2int (int2u X_21)) X_21) :pattern ((int2u X_21)))))
(assert
  (forall ((X_21 Real))
  (! (= (u2real (real2u X_21)) X_21) :pattern ((real2u X_21)))))
(assert
  (forall ((X_21 u))
  (! (= (tla__in X_21 tla__Int) (exists ((N_20 Int)) (= X_21 (int2u N_20)))) :pattern ((tla__in X_21 tla__Int)))))
(assert
  (forall ((M_19 Real) (N_20 Real))
  (! (= (tla__plus (real2u M_19) (real2u N_20)) (real2u (+ M_19 N_20))) :pattern ((tla__plus (real2u M_19) (real2u N_20))))))
(assert
  (forall ((M_19 Real) (N_20 Real))
  (! (= (tla__minus (real2u M_19) (real2u N_20)) (real2u (- M_19 N_20))) :pattern ((tla__minus (real2u M_19) (real2u N_20))))))
(assert
  (forall ((M_19 Real) (N_20 Real))
  (! (= (tla__lt (real2u M_19) (real2u N_20)) (< M_19 N_20)) :pattern ((tla__lt (real2u M_19) (real2u N_20))))))
(assert
  (forall ((M_19 Real) (N_20 Real))
  (! (= (tla__le (real2u M_19) (real2u N_20)) (<= M_19 N_20)) :pattern ((tla__le (real2u M_19) (real2u N_20))))))
(assert
  (forall ((M_19 Real) (N_20 Real) (Z_23 u))
  (=
  (tla__in Z_23 (tla__Range (real2u M_19) (real2u N_20)))
  (exists ((X_21 Real))
  (and (= Z_23 (real2u X_21)) (<= M_19 X_21) (<= X_21 N_20))))))
(assert
  (forall ((M_19 Real) (N_20 Real) (X_21 Real) (Y_22 Real))
  (=>
  (and
  (or (<= M_19 N_20) (<= X_21 Y_22))
  (=
  (tla__Range (real2u M_19) (real2u N_20))
  (tla__Range (real2u X_21) (real2u Y_22))))
  (and (= M_19 X_21) (= N_20 Y_22)))))
(assert
  (forall ((M_19 Real) (N_20 Real))
  (= (= (tla__Range (real2u M_19) (real2u N_20)) tla__emptyset) (< N_20 M_19))))
(assert
  (forall ((S_24 u) (T_25 u))
  (=>
  (forall ((X_21 u)) (= (tla__in X_21 S_24) (tla__in X_21 T_25)))
  (= S_24 T_25))))
(assert
  (forall ((X_21 u))
  (! (= (tla__in X_21 tla__emptyset) false) :pattern ((tla__in X_21 tla__emptyset)))))
(assert
  (forall ((F_27 u) (G_28 u))
  (=>
  (and
  (tla__isAFcn F_27) (tla__isAFcn G_28)
  (forall ((X_21 u))
  (= (tla__in X_21 (tla__DOMAIN F_27)) (tla__in X_21 (tla__DOMAIN G_28)))))
  (= (tla__DOMAIN F_27) (tla__DOMAIN G_28)))))
(assert
  (forall ((F_27 u) (G_28 u))
  (=>
  (and
  (tla__isAFcn F_27) (tla__isAFcn G_28)
  (= (tla__DOMAIN F_27) (tla__DOMAIN G_28))
  (forall ((X_21 u))
  (=>
  (tla__in X_21 (tla__DOMAIN G_28))
  (= (tla__fcnapp F_27 X_21) (tla__fcnapp G_28 X_21)))))
  (= F_27 G_28))))
(assert
  (forall ((S_24 u))
  (= (= S_24 tla__tuple0) (= (tla__DOMAIN S_24) tla__emptyset))))
(assert (forall ((S_24 u)) (= (= S_24 tla__tuple0) (= (tla__Len S_24) 0))))
(assert
  (forall ((S_24 u) (T_25 u))
  (=
  (tla__in S_24 (tla__Seq T_25))
  (and
  (<= 0 (tla__Len S_24)) (tla__isAFcn S_24)
  (= (tla__DOMAIN S_24) (tla__Range (int2u 1) (int2u (tla__Len S_24))))
  (forall ((I_26 Int))
  (=>
  (and (<= 1 I_26) (<= I_26 (tla__Len S_24)))
  (tla__in (tla__fcnapp S_24 (int2u I_26)) T_25)))))))
(assert
  (forall ((S_24 u) (N_20 Int))
  (=>
  (<= 0 N_20)
  (=
  (= (tla__DOMAIN S_24) (tla__Range (int2u 1) (int2u N_20)))
  (= (tla__Len S_24) N_20)))))
(assert (forall ((S_24 u)) (<= 0 (tla__Len S_24))))

;; Theorem to be Proved
(assert (not
  (and
    (or
      (=
        (int2u
          (+
            (tla__plus
              (tla__Len a_CONSTANTunde_sunde_a)
              (tla__Len a_CONSTANTunde_tunde_a)) 1))
        (int2u
          (+
            (+ (tla__Len a_CONSTANTunde_sunde_a) 1)
            (tla__Len a_CONSTANTunde_tunde_a))))
      (and
        (tla__lt
          (int2u
            (tla__plus
              (tla__Len a_CONSTANTunde_sunde_a)
              (tla__Len a_CONSTANTunde_tunde_a))) (int2u 1))
        (tla__lt
          (int2u
            (-
              (+
                (+ (tla__Len a_CONSTANTunde_sunde_a) 1)
                (tla__Len a_CONSTANTunde_tunde_a)) 1)) (int2u 1))))
    (forall ((a_v6a Int))
      (=>
        (and
          (<= 1 a_v6a)
          (tla__le
            (int2u a_v6a) (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))))
        (=
          (ite
            (tla__le (int2u a_v6a) (int2u (tla__Len a_CONSTANTunde_sunde_a)))
            (ite
              (tla__in (int2u a_v6a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp a_CONSTANTunde_sunde_a (int2u a_v6a))
              (tla__unspec a_CONSTANTunde_sunde_a (int2u a_v6a)))
            (ite
              (tla__in
                (int2u a_v6a)
                (tla__Range
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_sunde_a)
                      (tla__Len a_CONSTANTunde_tunde_a)))))
              (ite
                (tla__in
                  (int2u (- a_v6a (tla__Len a_CONSTANTunde_sunde_a)))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v6a (tla__Len a_CONSTANTunde_sunde_a))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v6a (tla__Len a_CONSTANTunde_sunde_a)))))
              a_newvarunde_unde_7a))
          (ite
            (tla__le (int2u a_v6a) (int2u (tla__Len a_CONSTANTunde_sunde_a)))
            (ite
              (tla__in (int2u a_v6a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp a_CONSTANTunde_sunde_a (int2u a_v6a))
              (tla__unspec a_CONSTANTunde_sunde_a (int2u a_v6a)))
            (ite
              (=
                (int2u a_v6a) (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1)))
              (ite
                (tla__in (int2u 1) (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp a_CONSTANTunde_tunde_a (int2u 1))
                (tla__unspec a_CONSTANTunde_tunde_a (int2u 1)))
              a_newvarunde_unde_8a)))))
    (forall ((a_v5a Real))
      (=>
        (and
          (tla__in (real2u a_v5a) tla__Int)
          (tla__le (int2u 1) (real2u a_v5a))
          (tla__le
            (real2u a_v5a) (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))))
        (=
          (ite
            (tla__le
              (real2u a_v5a) (int2u (tla__Len a_CONSTANTunde_sunde_a)))
            (ite
              (tla__in (real2u a_v5a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp a_CONSTANTunde_sunde_a (real2u a_v5a))
              (tla__unspec a_CONSTANTunde_sunde_a (real2u a_v5a)))
            (ite
              (tla__in
                (real2u a_v5a)
                (tla__Range
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_sunde_a)
                      (tla__Len a_CONSTANTunde_tunde_a)))))
              (ite
                (tla__in
                  (real2u
                    (tla__minus
                      a_v5a (int2u (tla__Len a_CONSTANTunde_sunde_a))))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (real2u
                    (tla__minus
                      a_v5a (int2u (tla__Len a_CONSTANTunde_sunde_a)))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (real2u
                    (tla__minus
                      a_v5a (int2u (tla__Len a_CONSTANTunde_sunde_a))))))
              a_newvarunde_unde_9a))
          (ite
            (tla__le
              (real2u a_v5a) (int2u (tla__Len a_CONSTANTunde_sunde_a)))
            (ite
              (tla__in (real2u a_v5a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp a_CONSTANTunde_sunde_a (real2u a_v5a))
              (tla__unspec a_CONSTANTunde_sunde_a (real2u a_v5a)))
            (ite
              (=
                (real2u a_v5a)
                (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1)))
              (ite
                (tla__in (int2u 1) (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp a_CONSTANTunde_tunde_a (int2u 1))
                (tla__unspec a_CONSTANTunde_tunde_a (int2u 1)))
              a_newvarunde_unde_10a)))))
    (forall ((a_v4a Int))
      (=>
        (and
          (<= 1 a_v4a)
          (tla__le
            (int2u (+ a_v4a 1)) (int2u (tla__Len a_CONSTANTunde_tunde_a))))
        (=
          (ite
            (and
              (tla__le
                (int2u 1)
                (int2u (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a)))
              (tla__le
                (int2u (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a))
                (int2u (tla__Len a_CONSTANTunde_sunde_a))))
            (ite
              (tla__in
                (int2u (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a))
                (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp
                a_CONSTANTunde_sunde_a
                (int2u (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a)))
              (tla__unspec
                a_CONSTANTunde_sunde_a
                (int2u (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a))))
            (ite
              (tla__in
                (int2u (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a))
                (tla__Range
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_sunde_a)
                      (tla__Len a_CONSTANTunde_tunde_a)))))
              (ite
                (tla__in
                  (int2u
                    (-
                      (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a)
                      (tla__Len a_CONSTANTunde_sunde_a)))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (int2u
                    (-
                      (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a)
                      (tla__Len a_CONSTANTunde_sunde_a))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (int2u
                    (-
                      (+ (+ (tla__Len a_CONSTANTunde_sunde_a) 1) a_v4a)
                      (tla__Len a_CONSTANTunde_sunde_a)))))
              a_newvarunde_unde_11a))
          (ite
            (tla__in
              (int2u (+ a_v4a 1)) (tla__DOMAIN a_CONSTANTunde_tunde_a))
            (tla__fcnapp a_CONSTANTunde_tunde_a (int2u (+ a_v4a 1)))
            (tla__unspec a_CONSTANTunde_tunde_a (int2u (+ a_v4a 1)))))))
    (forall ((a_v3a Real))
      (=>
        (and
          (tla__in (real2u a_v3a) tla__Int)
          (tla__le (int2u 1) (real2u a_v3a))
          (tla__le
            (real2u a_v3a) (int2u (- (tla__Len a_CONSTANTunde_tunde_a) 1))))
        (=
          (ite
            (and
              (tla__in
                (tla__plus
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (real2u a_v3a)) tla__Int)
              (tla__le
                (int2u 1)
                (tla__plus
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (real2u a_v3a)))
              (tla__le
                (tla__plus
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (real2u a_v3a)) (int2u (tla__Len a_CONSTANTunde_sunde_a))))
            (ite
              (tla__in
                (tla__plus
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (real2u a_v3a)) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp
                a_CONSTANTunde_sunde_a
                (tla__plus
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (real2u a_v3a)))
              (tla__unspec
                a_CONSTANTunde_sunde_a
                (tla__plus
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (real2u a_v3a))))
            (ite
              (tla__in
                (tla__plus
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (real2u a_v3a))
                (tla__Range
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_sunde_a)
                      (tla__Len a_CONSTANTunde_tunde_a)))))
              (ite
                (tla__in
                  (tla__minus
                    (tla__plus
                      (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                      (real2u a_v3a))
                    (int2u (tla__Len a_CONSTANTunde_sunde_a)))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (tla__minus
                    (tla__plus
                      (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                      (real2u a_v3a))
                    (int2u (tla__Len a_CONSTANTunde_sunde_a))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (tla__minus
                    (tla__plus
                      (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                      (real2u a_v3a))
                    (int2u (tla__Len a_CONSTANTunde_sunde_a)))))
              a_newvarunde_unde_13a))
          (ite
            (tla__in
              (tla__plus (real2u a_v3a) (int2u 1))
              (tla__DOMAIN a_CONSTANTunde_tunde_a))
            (tla__fcnapp
              a_CONSTANTunde_tunde_a (tla__plus (real2u a_v3a) (int2u 1)))
            (tla__unspec
              a_CONSTANTunde_tunde_a (tla__plus (real2u a_v3a) (int2u 1)))))))
    (forall ((a_v2a Int))
      (=>
        (tla__in
          (int2u a_v2a)
          (tla__Range
            (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 2))
            (int2u
              (-
                (+
                  (+ (tla__Len a_CONSTANTunde_sunde_a) 1)
                  (tla__Len a_CONSTANTunde_tunde_a)) 1))))
        (=
          (ite
            (and
              (<= 1 a_v2a)
              (tla__le
                (int2u a_v2a) (int2u (tla__Len a_CONSTANTunde_sunde_a))))
            (ite
              (tla__in (int2u a_v2a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp a_CONSTANTunde_sunde_a (int2u a_v2a))
              (tla__unspec a_CONSTANTunde_sunde_a (int2u a_v2a)))
            (ite
              (tla__in
                (int2u a_v2a)
                (tla__Range
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_sunde_a)
                      (tla__Len a_CONSTANTunde_tunde_a)))))
              (ite
                (tla__in
                  (int2u (- a_v2a (tla__Len a_CONSTANTunde_sunde_a)))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v2a (tla__Len a_CONSTANTunde_sunde_a))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (int2u (- a_v2a (tla__Len a_CONSTANTunde_sunde_a)))))
              a_newvarunde_unde_15a))
          (ite
            (and
              (tla__le
                (int2u (+ 2 (tla__Len a_CONSTANTunde_sunde_a))) (int2u a_v2a))
              (tla__le
                (int2u a_v2a)
                (int2u
                  (tla__plus
                    (tla__Len a_CONSTANTunde_tunde_a)
                    (tla__Len a_CONSTANTunde_sunde_a)))))
            (ite
              (tla__in
                (int2u (- a_v2a (tla__Len a_CONSTANTunde_sunde_a)))
                (tla__DOMAIN a_CONSTANTunde_tunde_a))
              (tla__fcnapp
                a_CONSTANTunde_tunde_a
                (int2u (- a_v2a (tla__Len a_CONSTANTunde_sunde_a))))
              (tla__unspec
                a_CONSTANTunde_tunde_a
                (int2u (- a_v2a (tla__Len a_CONSTANTunde_sunde_a)))))
            a_newvarunde_unde_16a))))
    (forall ((a_v1a Real))
      (=>
        (tla__in
          (real2u a_v1a)
          (tla__Range
            (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 2))
            (int2u
              (-
                (+
                  (+ (tla__Len a_CONSTANTunde_sunde_a) 1)
                  (tla__Len a_CONSTANTunde_tunde_a)) 1))))
        (=
          (ite
            (and
              (tla__in (real2u a_v1a) tla__Int)
              (tla__le (int2u 1) (real2u a_v1a))
              (tla__le
                (real2u a_v1a) (int2u (tla__Len a_CONSTANTunde_sunde_a))))
            (ite
              (tla__in (real2u a_v1a) (tla__DOMAIN a_CONSTANTunde_sunde_a))
              (tla__fcnapp a_CONSTANTunde_sunde_a (real2u a_v1a))
              (tla__unspec a_CONSTANTunde_sunde_a (real2u a_v1a)))
            (ite
              (tla__in
                (real2u a_v1a)
                (tla__Range
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))
                  (int2u
                    (tla__plus
                      (tla__Len a_CONSTANTunde_sunde_a)
                      (tla__Len a_CONSTANTunde_tunde_a)))))
              (ite
                (tla__in
                  (real2u
                    (tla__minus
                      a_v1a (int2u (tla__Len a_CONSTANTunde_sunde_a))))
                  (tla__DOMAIN a_CONSTANTunde_tunde_a))
                (tla__fcnapp
                  a_CONSTANTunde_tunde_a
                  (real2u
                    (tla__minus
                      a_v1a (int2u (tla__Len a_CONSTANTunde_sunde_a)))))
                (tla__unspec
                  a_CONSTANTunde_tunde_a
                  (real2u
                    (tla__minus
                      a_v1a (int2u (tla__Len a_CONSTANTunde_sunde_a))))))
              a_newvarunde_unde_17a))
          (ite
            (and
              (tla__in
                (tla__minus
                  (real2u a_v1a)
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))) tla__Int)
              (tla__le
                (int2u 1)
                (tla__minus
                  (real2u a_v1a)
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1))))
              (tla__le
                (tla__minus
                  (real2u a_v1a)
                  (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1)))
                (int2u (- (tla__Len a_CONSTANTunde_tunde_a) 1))))
            (ite
              (tla__in
                (tla__plus
                  (tla__minus
                    (real2u a_v1a)
                    (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1)))
                  (int2u 1)) (tla__DOMAIN a_CONSTANTunde_tunde_a))
              (tla__fcnapp
                a_CONSTANTunde_tunde_a
                (tla__plus
                  (tla__minus
                    (real2u a_v1a)
                    (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1)))
                  (int2u 1)))
              (tla__unspec
                a_CONSTANTunde_tunde_a
                (tla__plus
                  (tla__minus
                    (real2u a_v1a)
                    (int2u (+ (tla__Len a_CONSTANTunde_sunde_a) 1)))
                  (int2u 1)))) a_newvarunde_unde_18a)))))))
(assert (tla__in a_CONSTANTunde_sunde_a (tla__Seq a_CONSTANTunde_Sunde_a)))
(assert (tla__in a_CONSTANTunde_tunde_a (tla__Seq a_CONSTANTunde_Sunde_a)))
(assert (not (= a_CONSTANTunde_tunde_a tla__tuple0)))

(check-sat)
(exit)

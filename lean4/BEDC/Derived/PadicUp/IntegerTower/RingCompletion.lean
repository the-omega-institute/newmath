import BEDC.Derived.PadicUp.IntegerTower

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

def natSubUnary : BHist -> BHist -> BHist
  | BHist.Empty, _ => BHist.Empty
  | BHist.e0 _, _ => BHist.Empty
  | M, BHist.Empty => M
  | M, BHist.e0 _ => M
  | BHist.e1 Mtail, BHist.e1 rtail => natSubUnary Mtail rtail

theorem natSubUnary_unary {M r : BHist} :
    UnaryHistory M -> UnaryHistory (natSubUnary M r) := by
  intro MUnary
  induction M generalizing r with
  | Empty =>
      unfold natSubUnary
      exact unary_empty
  | e0 _ =>
      cases MUnary
  | e1 Mtail ih =>
      cases r with
      | Empty =>
          exact MUnary
      | e0 _ =>
          exact MUnary
      | e1 rtail =>
          exact ih (unary_e1_inversion MUnary)

theorem natSubUnary_self_empty {r : BHist} :
    UnaryHistory r -> hsame (natSubUnary r r) BHist.Empty := by
  intro rUnary
  induction r with
  | Empty =>
      rfl
  | e0 _ =>
      cases rUnary
  | e1 rtail ih =>
      exact ih (unary_e1_inversion rUnary)

theorem natSubUnary_empty_right {M : BHist} :
    UnaryHistory M -> hsame (natSubUnary M BHist.Empty) M := by
  intro MUnary
  cases M with
  | Empty => rfl
  | e0 _ => cases MUnary
  | e1 _ => rfl

theorem natSubUnary_prefix_hsame {M r tail : BHist} :
    UnaryHistory M -> UnaryHistory r -> UnaryHistory tail -> Cont r tail M ->
      hsame (natSubUnary M r) tail := by
  intro MUnary rUnary tailUnary prefCont
  induction M generalizing r tail with
  | Empty =>
      have parts := cont_empty_result_inversion prefCont
      cases parts.right
      rfl
  | e0 _ =>
      cases MUnary
  | e1 Mtail ih =>
      cases r with
      | Empty =>
          exact cont_left_unit_result prefCont
      | e0 _ =>
          cases rUnary
      | e1 rtail =>
          cases tail with
          | Empty =>
              have sameMR : hsame (BHist.e1 Mtail) (BHist.e1 rtail) :=
                cont_right_unit_iff.mp prefCont
              cases sameMR
              exact natSubUnary_self_empty rUnary
          | e0 _ =>
              cases tailUnary
          | e1 tailtail =>
              have tailtailUnary : UnaryHistory tailtail :=
                unary_e1_inversion tailUnary
              have loweredPrefix : Cont rtail (BHist.e1 tailtail) Mtail := by
                exact cont_intro
                  ((BHist.e1.inj prefCont).trans
                    (unary_append_e1_left (h := tailtail) (k := rtail)
                      tailtailUnary))
              exact ih (unary_e1_inversion MUnary) (unary_e1_inversion rUnary)
                tailUnary loweredPrefix

def natComplementMod (M r : BHist) : BHist :=
  natModFn M (natSubUnary M (natModFn M r))

theorem natComplementMod_unary {M r : BHist} :
    UnaryHistory M -> UnaryHistory (natComplementMod M r) := by
  intro MUnary
  unfold natComplementMod
  exact natModFn_unary_all M (natSubUnary M (natModFn M r))

theorem natComplementMod_hsame_arg_transport {M a b : BHist} :
    hsame a b -> hsame (natComplementMod M a) (natComplementMod M b) := by
  intro same
  cases same
  rfl

theorem natModFn_self_zero {M : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      hsame (natModFn M M) BHist.Empty := by
  intro MUnary MNonempty
  exact (dvd_iff_mod_zero MUnary MNonempty MUnary).mp
    (NatDivides_reflexive_pair MUnary).right

theorem natComplementMod_add_right_zero {M r : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> UnaryHistory r ->
        hsame
          (natModFn M
            (BEDC.FKernel.Cont.append (natComplementMod M r) (natModFn M r)))
          BHist.Empty := by
  intro MUnary MNonempty rUnary
  unfold natComplementMod
  have remUnary : UnaryHistory (natModFn M r) :=
    natModFn_unary MUnary rUnary MNonempty
  have remStrict : NatUnaryStrictPrefix (natModFn M r) M :=
    natModFn_lt MUnary rUnary MNonempty
  have subUnary : UnaryHistory (natSubUnary M (natModFn M r)) := natSubUnary_unary MUnary
  have raw :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append
            (natModFn M (natSubUnary M (natModFn M r))) (natModFn M r)))
        (natModFn M
          (BEDC.FKernel.Cont.append (natSubUnary M (natModFn M r)) (natModFn M r))) := by
    exact hsame_symm
      (natModFn_add_congruence MUnary MNonempty
        subUnary remUnary (natModFn_unary MUnary subUnary MNonempty) remUnary
        (hsame_symm (mod_idem MUnary MNonempty subUnary))
        (hsame_refl _))
  have sumIsM :
      hsame
        (BEDC.FKernel.Cont.append (natSubUnary M (natModFn M r)) (natModFn M r)) M := by
    cases remStrict with
    | intro tail tailData =>
        have subSame : hsame (natSubUnary M (natModFn M r)) tail :=
          natSubUnary_prefix_hsame MUnary remUnary tailData.left tailData.right.right
        cases subSame
        exact (unary_append_comm tailData.left remUnary).trans
          (hsame_symm tailData.right.right)
  exact hsame_trans raw
    (hsame_trans
      (natModFn_hsame_arg_transport (M := M) sumIsM)
      (natModFn_self_zero MUnary MNonempty))

theorem natComplementMod_add_left_zero {M r : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> UnaryHistory r ->
        hsame
          (natModFn M
            (BEDC.FKernel.Cont.append (natModFn M r) (natComplementMod M r)))
          BHist.Empty := by
  intro MUnary MNonempty rUnary
  have compUnary : UnaryHistory (natComplementMod M r) :=
    natComplementMod_unary MUnary
  have remUnary : UnaryHistory (natModFn M r) :=
    natModFn_unary MUnary rUnary MNonempty
  have commuted :
      hsame
        (natModFn M (BEDC.FKernel.Cont.append (natModFn M r) (natComplementMod M r)))
        (natModFn M (BEDC.FKernel.Cont.append (natComplementMod M r) (natModFn M r))) :=
    natModFn_hsame_arg_transport (M := M)
      (unary_append_comm remUnary compUnary)
  exact hsame_trans commuted
    (natComplementMod_add_right_zero MUnary MNonempty rUnary)

theorem natComplementMod_add_right_zero_of_strict {M r : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> UnaryHistory r ->
      NatUnaryStrictPrefix r M ->
        hsame
          (natModFn M (BEDC.FKernel.Cont.append (natComplementMod M r) r))
          BHist.Empty := by
  intro MUnary MNonempty rUnary rStrict
  have remSame : hsame (natModFn M r) r :=
    natModFn_of_strict MUnary MNonempty rUnary rStrict
  have raw :=
    natComplementMod_add_right_zero MUnary MNonempty rUnary
  exact hsame_trans
    (natModFn_append_hsame_transport (hsame_refl _) (hsame_symm remSame))
    raw

theorem natComplementMod_add_left_zero_of_strict {M r : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) -> UnaryHistory r ->
      NatUnaryStrictPrefix r M ->
        hsame
          (natModFn M (BEDC.FKernel.Cont.append r (natComplementMod M r)))
          BHist.Empty := by
  intro MUnary MNonempty rUnary rStrict
  have remSame : hsame (natModFn M r) r :=
    natModFn_of_strict MUnary MNonempty rUnary rStrict
  have raw :=
    natComplementMod_add_left_zero MUnary MNonempty rUnary
  exact hsame_trans
    (natModFn_append_hsame_transport (hsame_symm remSame) (hsame_refl _))
    raw

theorem natDivides_nonempty_strict_absurd {M t : BHist} :
    UnaryHistory M -> UnaryHistory t -> (t = BHist.Empty -> False) ->
      NatUnaryStrictPrefix t M -> NatDivides M t -> False := by
  intro MUnary tUnary tNonempty tStrict dividesT
  have boundary :=
    NatDivides_nonempty_result_boundary dividesT tUnary
      (fun tEmpty => tNonempty tEmpty)
  cases boundary with
  | inl sameMT =>
      cases tStrict with
      | intro tail tailData =>
          exact NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
            tailData.left tailData.right.left tailData.right.right
            (hsame_symm sameMT)
  | inr MLtT =>
      exact NatUnaryStrictPrefix_asymm MLtT tStrict

theorem NatUnaryStrictPrefix_tail_lt_target {a b tail M : BHist} :
    UnaryHistory a -> UnaryHistory tail -> NatUnaryStrictPrefix a b ->
      Cont a tail b -> NatUnaryStrictPrefix b M -> NatUnaryStrictPrefix tail M := by
  intro aUnary tailUnary _aLtB tailCont bLtM
  cases a with
  | Empty =>
      have sameBTail : hsame b tail := cont_left_unit_result tailCont
      exact NatUnaryStrictPrefix_hsame_source_transport_for_divides_closure bLtM
        sameBTail
  | e0 _ =>
      cases aUnary
  | e1 atail =>
      have aPositive : NatUnaryStrictPrefix BHist.Empty (BHist.e1 atail) :=
        ⟨BHist.e1 atail, aUnary, (fun empty => by cases empty), cont_left_unit _⟩
      have tailLtB : NatUnaryStrictPrefix tail b :=
        NatAdd_left_positive_right_strict
          (And.intro aUnary (And.intro tailUnary tailCont)) aPositive
      exact NatUnaryStrictPrefix_trans tailLtB bLtM

theorem natModFn_add_inverse_strict_absurd {M r a b : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory r -> UnaryHistory a -> UnaryHistory b ->
        NatUnaryStrictPrefix a M -> NatUnaryStrictPrefix b M ->
          hsame (natModFn M (BEDC.FKernel.Cont.append a r)) BHist.Empty ->
            hsame (natModFn M (BEDC.FKernel.Cont.append b r)) BHist.Empty ->
              NatUnaryStrictPrefix a b -> False := by
  intro MUnary MNonempty rUnary aUnary bUnary aStrict bStrict aZero bZero aLtB
  have dividesA :
      NatDivides M (BEDC.FKernel.Cont.append a r) :=
    (dvd_iff_mod_zero MUnary MNonempty (unary_append_closed aUnary rUnary)).mpr
      aZero
  have dividesB :
      NatDivides M (BEDC.FKernel.Cont.append b r) :=
    (dvd_iff_mod_zero MUnary MNonempty (unary_append_closed bUnary rUnary)).mpr
      bZero
  cases aLtB with
  | intro tail tailData =>
      have tailUnary : UnaryHistory tail := tailData.left
      have tailNonempty : tail = BHist.Empty -> False := tailData.right.left
      have bDisplay :
          hsame (BEDC.FKernel.Cont.append b r)
            (BEDC.FKernel.Cont.append
              (BEDC.FKernel.Cont.append a r) tail) := by
        calc
          BEDC.FKernel.Cont.append b r =
            BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append a tail) r :=
              congrArg (fun h => BEDC.FKernel.Cont.append h r)
                tailData.right.right
          _ = BEDC.FKernel.Cont.append a
              (BEDC.FKernel.Cont.append tail r) :=
              append_assoc a tail r
          _ = BEDC.FKernel.Cont.append a
              (BEDC.FKernel.Cont.append r tail) :=
              congrArg (fun h => BEDC.FKernel.Cont.append a h)
                (unary_append_comm tailUnary rUnary)
          _ = BEDC.FKernel.Cont.append
              (BEDC.FKernel.Cont.append a r) tail :=
              (append_assoc a r tail).symm
      have dividesDisplayed :
          NatDivides M
            (BEDC.FKernel.Cont.append
              (BEDC.FKernel.Cont.append a r) tail) :=
        (NatDivides_dividend_hsame_transport dividesB bDisplay).right
      have addDisplayed :
          NatAdd (BEDC.FKernel.Cont.append a r) tail
            (BEDC.FKernel.Cont.append
              (BEDC.FKernel.Cont.append a r) tail) :=
        NatAdd_append_self (unary_append_closed aUnary rUnary) tailUnary
      have dividesTail : NatDivides M tail :=
        dvd_tail_of_dvd_sum MUnary MNonempty addDisplayed dividesA dividesDisplayed
      have tailStrictM :
          NatUnaryStrictPrefix tail M :=
        NatUnaryStrictPrefix_tail_lt_target aUnary tailUnary
          ⟨tail, tailUnary, tailNonempty, tailData.right.right⟩
          tailData.right.right bStrict
      exact natDivides_nonempty_strict_absurd MUnary tailUnary tailNonempty
        tailStrictM dividesTail

theorem natModFn_add_inverse_unique {M r a b : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory r -> UnaryHistory a -> UnaryHistory b ->
        NatUnaryStrictPrefix a M -> NatUnaryStrictPrefix b M ->
          hsame (natModFn M (BEDC.FKernel.Cont.append a r)) BHist.Empty ->
            hsame (natModFn M (BEDC.FKernel.Cont.append b r)) BHist.Empty ->
              hsame a b := by
  intro MUnary MNonempty rUnary aUnary bUnary aStrict bStrict aZero bZero
  have total := NatUnaryPrefix_trichotomy_hsame_strict aUnary bUnary
  cases total with
  | inl same =>
      exact same
  | inr strictCases =>
      cases strictCases with
      | inl aLtB =>
          exact False.elim
            (natModFn_add_inverse_strict_absurd MUnary MNonempty rUnary
              aUnary bUnary aStrict bStrict aZero bZero aLtB)
      | inr bLtA =>
          exact False.elim
            (natModFn_add_inverse_strict_absurd MUnary MNonempty rUnary
              bUnary aUnary bStrict aStrict bZero aZero bLtA)

theorem natComplementMod_reduce_compat_of_dvd {M K v : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory K -> (hsame K BHist.Empty -> False) ->
        UnaryHistory v -> NatDivides M K ->
          hsame (natModFn M (natComplementMod K v))
            (natComplementMod M (natModFn M v)) := by
  intro MUnary MNonempty KUnary KNonempty vUnary dividesMK
  have compKUnary : UnaryHistory (natComplementMod K v) :=
    natComplementMod_unary KUnary
  have compMUnary : UnaryHistory (natComplementMod M (natModFn M v)) :=
    natComplementMod_unary MUnary
  have rMUnary : UnaryHistory (natModFn M v) :=
    natModFn_unary MUnary vUnary MNonempty
  have leftSumZero :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append
            (natModFn M (natComplementMod K v))
            (natModFn M v)))
        BHist.Empty := by
    have reduceSum :
        hsame
          (natModFn M
            (BEDC.FKernel.Cont.append
              (natModFn M (natComplementMod K v))
              (natModFn M v)))
          (natModFn M
            (BEDC.FKernel.Cont.append (natComplementMod K v) v)) := by
      exact natModFn_add_congruence MUnary MNonempty
        (natModFn_unary MUnary compKUnary MNonempty) rMUnary compKUnary vUnary
        (mod_idem MUnary MNonempty compKUnary)
        (natModFn_rem_rem_of_dvd MUnary MNonempty MUnary MNonempty vUnary
          (NatDivides_reflexive_pair MUnary).right)
    have KZero :
        hsame
          (natModFn K
            (BEDC.FKernel.Cont.append (natComplementMod K v) (natModFn K v)))
          BHist.Empty :=
      natComplementMod_add_right_zero KUnary KNonempty vUnary
    have vReduce :
        hsame
          (natModFn K (BEDC.FKernel.Cont.append (natComplementMod K v) v))
          (natModFn K
            (BEDC.FKernel.Cont.append (natComplementMod K v) (natModFn K v))) := by
      exact natModFn_add_congruence KUnary KNonempty
        compKUnary vUnary compKUnary (natModFn_unary KUnary vUnary KNonempty)
        (hsame_refl _)
        (hsame_symm (mod_idem KUnary KNonempty vUnary))
    have sumModKZero :
        hsame
          (natModFn K (BEDC.FKernel.Cont.append (natComplementMod K v) v))
          BHist.Empty :=
      hsame_trans vReduce KZero
    have dividesKSum :
        NatDivides K (BEDC.FKernel.Cont.append (natComplementMod K v) v) :=
      (dvd_iff_mod_zero KUnary KNonempty (unary_append_closed compKUnary vUnary)).mpr
        sumModKZero
    have dividesMSum :
        NatDivides M (BEDC.FKernel.Cont.append (natComplementMod K v) v) :=
      NatDivides_transitive dividesMK dividesKSum
    have MZero :
        hsame
          (natModFn M (BEDC.FKernel.Cont.append (natComplementMod K v) v))
          BHist.Empty :=
      (dvd_iff_mod_zero MUnary MNonempty (unary_append_closed compKUnary vUnary)).mp
        dividesMSum
    exact hsame_trans reduceSum MZero
  have rightSumZero :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append
            (natComplementMod M (natModFn M v))
            (natModFn M v)))
        BHist.Empty :=
    hsame_trans
      (natModFn_append_hsame_transport (hsame_refl _)
        (hsame_symm (mod_idem MUnary MNonempty vUnary)))
      (natComplementMod_add_right_zero MUnary MNonempty rMUnary)
  have leftUnary : UnaryHistory (natModFn M (natComplementMod K v)) :=
    natModFn_unary MUnary compKUnary MNonempty
  have rightUnary : UnaryHistory (natComplementMod M (natModFn M v)) :=
    compMUnary
  have leftStrict : NatUnaryStrictPrefix (natModFn M (natComplementMod K v)) M :=
    natModFn_lt MUnary compKUnary MNonempty
  have rightStrict : NatUnaryStrictPrefix (natComplementMod M (natModFn M v)) M :=
    natModFn_lt MUnary (natSubUnary_unary MUnary) MNonempty
  exact natModFn_add_inverse_unique MUnary MNonempty rMUnary
    leftUnary rightUnary leftStrict rightStrict leftSumZero rightSumZero

theorem complement_reduce_compat {p N v : BHist}
    (prime : NatPrime p) (NUnary : UnaryHistory N) (vUnary : UnaryHistory v) :
      hsame
        (natModFn (pPowCanon p N)
          (natComplementMod (pPowCanon p (BHist.e1 N)) v))
        (natComplementMod (pPowCanon p N)
          (natModFn (pPowCanon p N) v)) := by
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have KUnary : UnaryHistory (pPowCanon p (BHist.e1 N)) :=
    pPowCanon_unary p (BHist.e1 N)
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime NUnary
  have KNonempty : hsame (pPowCanon p (BHist.e1 N)) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime prime (unary_e1_closed NUnary)
  have pref : NatUnaryPrefix N (BHist.e1 N) :=
    ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, cont_intro rfl⟩
  have dividesMK : NatDivides (pPowCanon p N) (pPowCanon p (BHist.e1 N)) :=
    pow_dvd_pow_of_le prime NUnary (unary_e1_closed NUnary) pref
  exact natComplementMod_reduce_compat_of_dvd MUnary MNonempty KUnary KNonempty
    vUnary dividesMK

def zpNegTrunc (p N : BHist) (prime : NatPrime p) (NUnary : UnaryHistory N)
    (x : ZpTrunc p N) : ZpTrunc p N :=
  fromNatModPow p N (natComplementMod (pPowCanon p N) x.val) prime NUnary

theorem zpNeg_compat (p : BHist) (x : ZpInt p) :
    ZpCompatible p x.prime
      (fun N NUnary => zpNegTrunc p N x.prime NUnary (x.trunc N NUnary)) := by
  intro N NUnary
  unfold reduce zpNegTrunc fromNatModPow ZpEqTrunc natMod
  have KUnary : UnaryHistory (pPowCanon p (BHist.e1 N)) :=
    pPowCanon_unary p (BHist.e1 N)
  have xNextUnary : UnaryHistory (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val :=
    BoundedNat_unary KUnary (x.trunc (BHist.e1 N) (unary_e1_closed NUnary))
  have xCompat := x.compat N NUnary
  unfold reduce fromNatModPow ZpEqTrunc natMod at xCompat
  have left :
      hsame
        (natModFn (pPowCanon p N)
          (natModFn (pPowCanon p (BHist.e1 N))
            (natComplementMod (pPowCanon p (BHist.e1 N))
              (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)))
        (natModFn (pPowCanon p N)
          (natComplementMod (pPowCanon p (BHist.e1 N))
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)) := by
    have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
    have KNonempty : hsame (pPowCanon p (BHist.e1 N)) BHist.Empty -> False :=
      pPowCanon_nonempty_of_prime x.prime (unary_e1_closed NUnary)
    exact natModFn_rem_rem_of_dvd MUnary
      (pPowCanon_nonempty_of_prime x.prime NUnary)
      KUnary KNonempty
      (natComplementMod_unary KUnary)
      (pow_dvd_pow_of_le x.prime NUnary (unary_e1_closed NUnary)
        ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty, cont_intro rfl⟩)
  have core :
      hsame
        (natModFn (pPowCanon p N)
          (natComplementMod (pPowCanon p (BHist.e1 N))
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val))
        (natComplementMod (pPowCanon p N)
          (natModFn (pPowCanon p N)
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val)) :=
    complement_reduce_compat x.prime NUnary xNextUnary
  have transport :
      hsame
        (natComplementMod (pPowCanon p N)
          (natModFn (pPowCanon p N)
            (x.trunc (BHist.e1 N) (unary_e1_closed NUnary)).val))
        (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val) := by
    exact natComplementMod_hsame_arg_transport xCompat
  have finalReduce :
      hsame
        (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val)
        (natModFn (pPowCanon p N)
          (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val)) := by
    have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
    have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
      pPowCanon_nonempty_of_prime x.prime NUnary
    unfold natComplementMod
    exact hsame_symm
      (mod_idem MUnary MNonempty
        (natSubUnary_unary MUnary))
  exact hsame_trans left (hsame_trans core (hsame_trans transport finalReduce))

def zpNeg (p : BHist) (x : ZpInt p) : ZpInt p :=
  { prime := x.prime
    trunc := fun N NUnary => zpNegTrunc p N x.prime NUnary (x.trunc N NUnary)
    compat := zpNeg_compat p x }

theorem zpAdd_neg_left (p : BHist) (x : ZpInt p) :
    ZpEq (zpAdd p (zpNeg p x) x) (zpZero p x.prime) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (natModFn (pPowCanon p N)
          (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val))
        (x.trunc N NUnary).val))
    (natModFn (pPowCanon p N) BHist.Empty)
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have leftToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val))
            (x.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val)
            (x.trunc N NUnary).val)) := by
    have compUnary : UnaryHistory
        (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val) :=
      natComplementMod_unary MUnary
    exact hsame_symm
      (natModFn_add_congruence MUnary MNonempty
        compUnary xUnary
        (natModFn_unary MUnary compUnary MNonempty) xUnary
        (hsame_symm (mod_idem MUnary MNonempty compUnary))
        (hsame_refl _))
  have rawZero :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natComplementMod (pPowCanon p N) (x.trunc N NUnary).val)
            (x.trunc N NUnary).val))
        BHist.Empty :=
    natComplementMod_add_right_zero_of_strict MUnary MNonempty xUnary
      (x.trunc N NUnary).isLt
  exact hsame_trans leftToRaw rawZero

theorem zpAdd_neg_right (p : BHist) (x : ZpInt p) :
    ZpEq (zpAdd p x (zpNeg p x)) (zpZero p x.prime) := by
  exact ZpEq_trans (zpAdd_comm p x (zpNeg p x))
    (zpAdd_neg_left p x)

theorem natMulFn_append_left_distrib_hsame {a b c : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
      hsame (natMulFn a (BEDC.FKernel.Cont.append b c))
        (BEDC.FKernel.Cont.append (natMulFn a b) (natMulFn a c)) := by
  intro aUnary bUnary cUnary
  induction c with
  | Empty =>
      change hsame (natMulFn a b)
        (BEDC.FKernel.Cont.append (natMulFn a b) BHist.Empty)
      exact hsame_symm (append_empty_right (natMulFn a b))
  | e0 _ =>
      cases cUnary
  | e1 ctail ih =>
      have tailUnary : UnaryHistory ctail := unary_e1_inversion cUnary
      change hsame
        (BEDC.FKernel.Cont.append (natMulFn a (BEDC.FKernel.Cont.append b ctail)) a)
        (BEDC.FKernel.Cont.append (natMulFn a b)
          (BEDC.FKernel.Cont.append (natMulFn a ctail) a))
      have ihSame :
          hsame (natMulFn a (BEDC.FKernel.Cont.append b ctail))
            (BEDC.FKernel.Cont.append (natMulFn a b) (natMulFn a ctail)) :=
        ih tailUnary
      exact hsame_trans
        (congrArg (fun h => BEDC.FKernel.Cont.append h a) ihSame)
        (BEDC.FKernel.Cont.append_assoc (natMulFn a b) (natMulFn a ctail) a)

theorem natMulFn_append_right_distrib_hsame {a b c : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
      hsame (natMulFn (BEDC.FKernel.Cont.append a b) c)
        (BEDC.FKernel.Cont.append (natMulFn a c) (natMulFn b c)) := by
  intro aUnary bUnary cUnary
  have abUnary : UnaryHistory (BEDC.FKernel.Cont.append a b) :=
    unary_append_closed aUnary bUnary
  have distributed :
      NatAdd (natMulFn a c) (natMulFn b c)
        (natMulFn (BEDC.FKernel.Cont.append a b) c) :=
    NatMul_cont_right_distrib aUnary bUnary cUnary (cont_intro rfl)
      (natMulFn_rel aUnary cUnary) (natMulFn_rel bUnary cUnary)
      (natMulFn_rel abUnary cUnary)
  exact distributed.right.right

theorem natModFn_mul_add_distrib {M a b c : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
        hsame
          (natModFn M (natMulFn a (BEDC.FKernel.Cont.append b c)))
          (natModFn M
            (BEDC.FKernel.Cont.append (natMulFn a b) (natMulFn a c))) := by
  intro MUnary MNonempty aUnary bUnary cUnary
  exact natModFn_hsame_arg_transport (M := M)
    (natMulFn_append_left_distrib_hsame aUnary bUnary cUnary)

theorem zpMul_add_distrib (p : BHist) (x y z : ZpInt p) :
    ZpEq (zpMul p x (zpAdd p y z))
      (zpAdd p (zpMul p x y) (zpMul p x z)) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn (x.trunc N NUnary).val
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))))
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))))
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have zUnary : UnaryHistory (z.trunc N NUnary).val :=
    BoundedNat_unary MUnary (z.trunc N NUnary)
  have yzUnary :
      UnaryHistory (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val) :=
    unary_append_closed yUnary zUnary
  have xyUnary : UnaryHistory (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val) :=
    natMulFn_unary xUnary yUnary
  have xzUnary : UnaryHistory (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val) :=
    natMulFn_unary xUnary zUnary
  have leftToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val
            (natModFn (pPowCanon p N)
              (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))))
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val
            (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))) :=
    natModFn_mul_right_reduce_same_mod MUnary MNonempty xUnary yzUnary
  have rawDistrib :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val
            (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))) :=
    natModFn_mul_add_distrib MUnary MNonempty xUnary yUnary zUnary
  have rawToRight :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
            (natModFn (pPowCanon p N)
              (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)))) := by
    exact mod_add_compat MUnary MNonempty xyUnary xzUnary
  exact hsame_trans leftToRaw (hsame_trans rawDistrib rawToRight)

theorem zpMul_add_distrib_right (p : BHist) (x y z : ZpInt p) :
    ZpEq (zpMul p (zpAdd p x y) z)
      (zpAdd p (zpMul p x z) (zpMul p y z)) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val))
        (z.trunc N NUnary).val))
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val))))
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have zUnary : UnaryHistory (z.trunc N NUnary).val :=
    BoundedNat_unary MUnary (z.trunc N NUnary)
  have xyRawUnary :
      UnaryHistory (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val) :=
    unary_append_closed xUnary yUnary
  have xzUnary : UnaryHistory (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val) :=
    natMulFn_unary xUnary zUnary
  have yzUnary : UnaryHistory (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val) :=
    natMulFn_unary yUnary zUnary
  have leftToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (natModFn (pPowCanon p N)
              (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val))
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn
            (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val)) :=
    natModFn_mul_left_reduce_same_mod MUnary MNonempty xyRawUnary zUnary
  have rawDistrib :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)
            (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val))) :=
    natModFn_hsame_arg_transport (M := pPowCanon p N)
      (natMulFn_append_right_distrib_hsame xUnary yUnary zUnary)
  have rawToRight :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)
            (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))
            (natModFn (pPowCanon p N)
              (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val)))) := by
    exact mod_add_compat MUnary MNonempty xzUnary yzUnary
  exact hsame_trans leftToRaw (hsame_trans rawDistrib rawToRight)

structure ZpIntDistribSemiringLaws (p : BHist) where
  add_comm : ∀ x y : ZpInt p, ZpEq (zpAdd p x y) (zpAdd p y x)
  add_assoc : ∀ x y z : ZpInt p,
    ZpEq (zpAdd p (zpAdd p x y) z) (zpAdd p x (zpAdd p y z))
  zero_add : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpAdd p (zpZero p prime) x) x
  add_zero : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpAdd p x (zpZero p prime)) x
  mul_comm : ∀ x y : ZpInt p, ZpEq (zpMul p x y) (zpMul p y x)
  mul_assoc : ∀ x y z : ZpInt p,
    ZpEq (zpMul p (zpMul p x y) z) (zpMul p x (zpMul p y z))
  one_mul : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpMul p (zpOne p prime) x) x
  mul_one : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpMul p x (zpOne p prime)) x
  left_distrib : ∀ x y z : ZpInt p,
    ZpEq (zpMul p x (zpAdd p y z))
      (zpAdd p (zpMul p x y) (zpMul p x z))
  right_distrib : ∀ x y z : ZpInt p,
    ZpEq (zpMul p (zpAdd p x y) z)
      (zpAdd p (zpMul p x z) (zpMul p y z))

def ZpInt_distrib_semiring_laws (p : BHist) : ZpIntDistribSemiringLaws p :=
  { add_comm := zpAdd_comm p
    add_assoc := zpAdd_assoc p
    zero_add := zpZero_add_left p
    add_zero := zpZero_add_right p
    mul_comm := zpMul_comm p
    mul_assoc := zpMul_assoc p
    one_mul := zpOne_mul_left p
    mul_one := zpOne_mul_right p
    left_distrib := zpMul_add_distrib p
    right_distrib := zpMul_add_distrib_right p }

structure ZpIntCommRingLaws (p : BHist) where
  add_comm : ∀ x y : ZpInt p, ZpEq (zpAdd p x y) (zpAdd p y x)
  add_assoc : ∀ x y z : ZpInt p,
    ZpEq (zpAdd p (zpAdd p x y) z) (zpAdd p x (zpAdd p y z))
  zero_add : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpAdd p (zpZero p prime) x) x
  add_zero : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpAdd p x (zpZero p prime)) x
  neg_add : ∀ x : ZpInt p,
    ZpEq (zpAdd p (zpNeg p x) x) (zpZero p x.prime)
  add_neg : ∀ x : ZpInt p,
    ZpEq (zpAdd p x (zpNeg p x)) (zpZero p x.prime)
  mul_comm : ∀ x y : ZpInt p, ZpEq (zpMul p x y) (zpMul p y x)
  mul_assoc : ∀ x y z : ZpInt p,
    ZpEq (zpMul p (zpMul p x y) z) (zpMul p x (zpMul p y z))
  one_mul : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpMul p (zpOne p prime) x) x
  mul_one : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpMul p x (zpOne p prime)) x
  left_distrib : ∀ x y z : ZpInt p,
    ZpEq (zpMul p x (zpAdd p y z))
      (zpAdd p (zpMul p x y) (zpMul p x z))
  right_distrib : ∀ x y z : ZpInt p,
    ZpEq (zpMul p (zpAdd p x y) z)
      (zpAdd p (zpMul p x z) (zpMul p y z))

def ZpInt_comm_ring_laws (p : BHist) : ZpIntCommRingLaws p :=
  { add_comm := zpAdd_comm p
    add_assoc := zpAdd_assoc p
    zero_add := zpZero_add_left p
    add_zero := zpZero_add_right p
    neg_add := zpAdd_neg_left p
    add_neg := zpAdd_neg_right p
    mul_comm := zpMul_comm p
    mul_assoc := zpMul_assoc p
    one_mul := zpOne_mul_left p
    mul_one := zpOne_mul_right p
    left_distrib := zpMul_add_distrib p
    right_distrib := zpMul_add_distrib_right p }

end BEDC.Derived.PadicUp

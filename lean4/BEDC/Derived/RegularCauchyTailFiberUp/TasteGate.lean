import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailFiberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailFiberUp : Type where
  | mk : (R0 R1 W0 W1 D0 D1 T A H C P N : BHist) → RegularCauchyTailFiberUp
  deriving DecidableEq

def regularCauchyTailFiberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailFiberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailFiberEncodeBHist h

def regularCauchyTailFiberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailFiberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailFiberDecodeBHist tail)

private theorem regularCauchyTailFiberDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailFiberDecodeBHist
        (regularCauchyTailFiberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailFiberToEventFlow :
    RegularCauchyTailFiberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T A H C P N =>
      [[BMark.b0],
        regularCauchyTailFiberEncodeBHist R0,
        [BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist W0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist W1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist D0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist D1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyTailFiberEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFiberEncodeBHist N]

def regularCauchyTailFiberFromEventFlow :
    EventFlow → Option RegularCauchyTailFiberUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | R0 :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | R1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W0 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W1 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | D0 :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | D1 :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | T :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | A :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | C :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | P :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | N :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (RegularCauchyTailFiberUp.mk
                                                                                                          (regularCauchyTailFiberDecodeBHist R0)
                                                                                                          (regularCauchyTailFiberDecodeBHist R1)
                                                                                                          (regularCauchyTailFiberDecodeBHist W0)
                                                                                                          (regularCauchyTailFiberDecodeBHist W1)
                                                                                                          (regularCauchyTailFiberDecodeBHist D0)
                                                                                                          (regularCauchyTailFiberDecodeBHist D1)
                                                                                                          (regularCauchyTailFiberDecodeBHist T)
                                                                                                          (regularCauchyTailFiberDecodeBHist A)
                                                                                                          (regularCauchyTailFiberDecodeBHist H)
                                                                                                          (regularCauchyTailFiberDecodeBHist C)
                                                                                                          (regularCauchyTailFiberDecodeBHist P)
                                                                                                          (regularCauchyTailFiberDecodeBHist N))
                                                                                                  | _ :: _ => none

private theorem regularCauchyTailFiber_round_trip :
    ∀ x : RegularCauchyTailFiberUp,
      regularCauchyTailFiberFromEventFlow
        (regularCauchyTailFiberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 W0 W1 D0 D1 T A H C P N =>
      change
        some
          (RegularCauchyTailFiberUp.mk
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist R0))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist R1))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist W0))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist W1))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist D0))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist D1))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist T))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist A))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist H))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist C))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist P))
            (regularCauchyTailFiberDecodeBHist
              (regularCauchyTailFiberEncodeBHist N))) =
          some (RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T A H C P N)
      rw [regularCauchyTailFiberDecode_encode_bhist R0,
        regularCauchyTailFiberDecode_encode_bhist R1,
        regularCauchyTailFiberDecode_encode_bhist W0,
        regularCauchyTailFiberDecode_encode_bhist W1,
        regularCauchyTailFiberDecode_encode_bhist D0,
        regularCauchyTailFiberDecode_encode_bhist D1,
        regularCauchyTailFiberDecode_encode_bhist T,
        regularCauchyTailFiberDecode_encode_bhist A,
        regularCauchyTailFiberDecode_encode_bhist H,
        regularCauchyTailFiberDecode_encode_bhist C,
        regularCauchyTailFiberDecode_encode_bhist P,
        regularCauchyTailFiberDecode_encode_bhist N]

private theorem regularCauchyTailFiberToEventFlow_injective
    {x y : RegularCauchyTailFiberUp} :
    regularCauchyTailFiberToEventFlow x =
      regularCauchyTailFiberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailFiberFromEventFlow
          (regularCauchyTailFiberToEventFlow x) =
        regularCauchyTailFiberFromEventFlow
          (regularCauchyTailFiberToEventFlow y) :=
    congrArg regularCauchyTailFiberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailFiber_round_trip x).symm
      (Eq.trans hread (regularCauchyTailFiber_round_trip y)))

instance regularCauchyTailFiberBHistCarrier :
    BHistCarrier RegularCauchyTailFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailFiberToEventFlow
  fromEventFlow := regularCauchyTailFiberFromEventFlow

instance regularCauchyTailFiberChapterTasteGate :
    ChapterTasteGate RegularCauchyTailFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailFiberFromEventFlow
        (regularCauchyTailFiberToEventFlow x) = some x
    exact regularCauchyTailFiber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailFiberToEventFlow_injective heq)

instance regularCauchyTailFiberFieldFaithful :
    FieldFaithful RegularCauchyTailFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T A H C P N =>
        [R0, R1, W0, W1, D0, D1, T, A, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk R0₁ R1₁ W0₁ W1₁ D0₁ D1₁ T₁ A₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk R0₂ R1₂ W0₂ W1₂ D0₂ D1₂ T₂ A₂ H₂ C₂ P₂ N₂ =>
            injection h with hR0 t1
            injection t1 with hR1 t2
            injection t2 with hW0 t3
            injection t3 with hW1 t4
            injection t4 with hD0 t5
            injection t5 with hD1 t6
            injection t6 with hT t7
            injection t7 with hA t8
            injection t8 with hH t9
            injection t9 with hC t10
            injection t10 with hP t11
            injection t11 with hN _
            cases hR0
            cases hR1
            cases hW0
            cases hW1
            cases hD0
            cases hD1
            cases hT
            cases hA
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance regularCauchyTailFiberNontrivial :
    Nontrivial RegularCauchyTailFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailFiberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyTailFiberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailFiberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RegularCauchyTailFiberTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailFiberDecodeBHist (regularCauchyTailFiberEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailFiberUp,
        regularCauchyTailFiberFromEventFlow (regularCauchyTailFiberToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyTailFiberUp,
          regularCauchyTailFiberToEventFlow x =
            regularCauchyTailFiberToEventFlow y → x = y) ∧
          regularCauchyTailFiberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyTailFiberDecode_encode_bhist
  · constructor
    · exact regularCauchyTailFiber_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyTailFiberToEventFlow_injective heq
      · rfl

def RegularCauchyTailFiberPacket [AskSetup] [PackageSetup]
    (r0 r1 w0 w1 d0 d1 t a h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
    UnaryHistory d0 ∧ UnaryHistory d1 ∧ UnaryHistory t ∧ UnaryHistory a ∧
      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
        Cont r0 w0 h ∧ Cont r1 w1 c ∧ Cont d0 d1 t ∧ Cont t a p ∧
          PkgSig bundle p pkg

theorem RegularCauchyTailFiberPacket_source_swap_stability [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n h' c' t' p' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      Cont r1 w1 h' →
        Cont r0 w0 c' →
          Cont d1 d0 t' →
            Cont t' a p' →
              PkgSig bundle p' pkg →
                RegularCauchyTailFiberPacket r1 r0 w1 w0 d1 d0 t' a h' c' p' n
                    bundle pkg ∧ hsame a a ∧ UnaryHistory t' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro packet hRoute cRoute tRoute pRoute pPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, d0Unary, d1Unary, _tUnary, aUnary,
    _hUnary, _cUnary, _pUnary, nUnary, _hRoute, _cRoute, _tRoute, _pRoute,
    _sourcePkg⟩ := packet
  have hUnary' : UnaryHistory h' := unary_cont_closed r1Unary w1Unary hRoute
  have cUnary' : UnaryHistory c' := unary_cont_closed r0Unary w0Unary cRoute
  have tUnary' : UnaryHistory t' := unary_cont_closed d1Unary d0Unary tRoute
  have pUnary' : UnaryHistory p' := unary_cont_closed tUnary' aUnary pRoute
  exact
    ⟨⟨r1Unary, r0Unary, w1Unary, w0Unary, d1Unary, d0Unary, tUnary', aUnary,
        hUnary', cUnary', pUnary', nUnary, hRoute, cRoute, tRoute, pRoute, pPkg⟩,
      hsame_refl a, tUnary'⟩

theorem RegularCauchyTailFiberPacket_classifier_exactness [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n r0' r1' w0' w1' d0' d1' t' a' h' c' p' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      hsame r0 r0' →
        hsame r1 r1' →
          hsame w0 w0' →
            hsame w1 w1' →
              hsame d0 d0' →
                hsame d1 d1' →
                  hsame t t' →
                    hsame a a' →
                      Cont r0' w0' h' →
                        Cont r1' w1' c' →
                          Cont t' a' p' →
                            PkgSig bundle p' pkg →
                              UnaryHistory h' ∧ UnaryHistory c' ∧ UnaryHistory p' ∧
                                hsame h h' ∧ hsame c c' ∧ hsame p p' ∧
                                  PkgSig bundle p' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameR0 sameR1 sameW0 sameW1 sameD0 sameD1 sameT sameA hRoute cRoute
    pRoute pPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, _d0Unary, _d1Unary, tUnary, aUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, oldHRoute, oldCRoute, _oldTRoute, oldPRoute,
    _oldPkg⟩ := packet
  have r0Unary' : UnaryHistory r0' := unary_transport r0Unary sameR0
  have r1Unary' : UnaryHistory r1' := unary_transport r1Unary sameR1
  have w0Unary' : UnaryHistory w0' := unary_transport w0Unary sameW0
  have w1Unary' : UnaryHistory w1' := unary_transport w1Unary sameW1
  have tUnary' : UnaryHistory t' := unary_transport tUnary sameT
  have aUnary' : UnaryHistory a' := unary_transport aUnary sameA
  have hUnary' : UnaryHistory h' := unary_cont_closed r0Unary' w0Unary' hRoute
  have cUnary' : UnaryHistory c' := unary_cont_closed r1Unary' w1Unary' cRoute
  have pUnary' : UnaryHistory p' := unary_cont_closed tUnary' aUnary' pRoute
  have sameH : hsame h h' :=
    cont_respects_hsame sameR0 sameW0 oldHRoute hRoute
  have sameC : hsame c c' :=
    cont_respects_hsame sameR1 sameW1 oldCRoute cRoute
  have sameP : hsame p p' :=
    cont_respects_hsame sameT sameA oldPRoute pRoute
  exact
    ⟨hUnary',
      cUnary',
      pUnary',
      sameH,
      sameC,
      sameP,
      pPkg⟩

theorem RegularCauchyTailFiberPacket_componentwise_transport [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n r0' r1' w0' w1' d0' d1' t' a' h' c' p'
      n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      hsame r0 r0' →
        hsame r1 r1' →
          hsame w0 w0' →
            hsame w1 w1' →
              hsame d0 d0' →
                hsame d1 d1' →
                  hsame t t' →
                    hsame a a' →
                      hsame n n' →
                        Cont r0' w0' h' →
                          Cont r1' w1' c' →
                            Cont d0' d1' t' →
                              Cont t' a' p' →
                                PkgSig bundle p' pkg →
                                  RegularCauchyTailFiberPacket r0' r1' w0' w1' d0'
                                      d1' t' a' h' c' p' n' bundle pkg ∧
                                    hsame h h' ∧ hsame c c' ∧ hsame p p' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameR0 sameR1 sameW0 sameW1 sameD0 sameD1 sameT sameA sameN hRoute
    cRoute tRoute pRoute pPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, d0Unary, d1Unary, tUnary, aUnary,
    _hUnary, _cUnary, _pUnary, nUnary, oldHRoute, oldCRoute, _oldTRoute, oldPRoute,
    _oldPkg⟩ := packet
  have r0Unary' : UnaryHistory r0' := unary_transport r0Unary sameR0
  have r1Unary' : UnaryHistory r1' := unary_transport r1Unary sameR1
  have w0Unary' : UnaryHistory w0' := unary_transport w0Unary sameW0
  have w1Unary' : UnaryHistory w1' := unary_transport w1Unary sameW1
  have d0Unary' : UnaryHistory d0' := unary_transport d0Unary sameD0
  have d1Unary' : UnaryHistory d1' := unary_transport d1Unary sameD1
  have tUnary' : UnaryHistory t' := unary_transport tUnary sameT
  have aUnary' : UnaryHistory a' := unary_transport aUnary sameA
  have nUnary' : UnaryHistory n' := unary_transport nUnary sameN
  have hUnary' : UnaryHistory h' := unary_cont_closed r0Unary' w0Unary' hRoute
  have cUnary' : UnaryHistory c' := unary_cont_closed r1Unary' w1Unary' cRoute
  have pUnary' : UnaryHistory p' := unary_cont_closed tUnary' aUnary' pRoute
  have sameH : hsame h h' :=
    cont_respects_hsame sameR0 sameW0 oldHRoute hRoute
  have sameC : hsame c c' :=
    cont_respects_hsame sameR1 sameW1 oldCRoute cRoute
  have sameP : hsame p p' :=
    cont_respects_hsame sameT sameA oldPRoute pRoute
  exact
    ⟨⟨r0Unary', r1Unary', w0Unary', w1Unary', d0Unary', d1Unary', tUnary',
        aUnary', hUnary', cUnary', pUnary', nUnary', hRoute, cRoute, tRoute,
        pRoute, pPkg⟩,
      sameH, sameC, sameP⟩

theorem RegularCauchyTailFiberPacket_seal_totality [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      Cont t a sealRead →
        PkgSig bundle sealRead pkg →
          UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
            UnaryHistory d0 ∧ UnaryHistory d1 ∧ UnaryHistory t ∧ UnaryHistory a ∧
              UnaryHistory sealRead ∧ Cont d0 d1 t ∧ Cont t a sealRead ∧
                PkgSig bundle p pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealRoute sealPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, d0Unary, d1Unary, tUnary, aUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _hRoute, _cRoute, tailRoute, _packetSealRoute,
    packetPkg⟩ := packet
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnary aUnary tailSealRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, d0Unary, d1Unary, tUnary, aUnary,
      sealUnary, tailRoute, tailSealRoute, packetPkg, sealPkg⟩

theorem RegularCauchyTailFiberPacket_source_seal_ledger_totality [AskSetup]
    [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      Cont t a handoff →
        PkgSig bundle handoff pkg →
          UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
            UnaryHistory d0 ∧ UnaryHistory d1 ∧ UnaryHistory t ∧ UnaryHistory a ∧
              UnaryHistory n ∧ UnaryHistory handoff ∧ Cont r0 w0 h ∧ Cont r1 w1 c ∧
                Cont d0 d1 t ∧ Cont t a p ∧ Cont t a handoff ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet handoffRoute handoffPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, d0Unary, d1Unary, tUnary, aUnary,
    _hUnary, _cUnary, _pUnary, nUnary, hRoute, cRoute, tailRoute, sealRoute,
    packetPkg⟩ := packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed tUnary aUnary handoffRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, d0Unary, d1Unary, tUnary, aUnary, nUnary,
      handoffUnary, hRoute, cRoute, tailRoute, sealRoute, handoffRoute, packetPkg,
      handoffPkg⟩

theorem RegularCauchyTailFiberPacket_meet_route [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n leftMeet rightMeet meet sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      Cont w0 d0 leftMeet →
        Cont w1 d1 rightMeet →
          Cont leftMeet rightMeet meet →
            Cont meet a sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory leftMeet ∧ UnaryHistory rightMeet ∧ UnaryHistory meet ∧
                  UnaryHistory sealRead ∧ hsame sealRead sealRead ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet leftRoute rightRoute meetRoute sealRoute sealPkg
  obtain ⟨_r0Unary, _r1Unary, w0Unary, w1Unary, d0Unary, d1Unary, _tUnary, aUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _sourceRoute, _classifierRoute, _tailRoute,
    _packetSealRoute, _packetPkg⟩ := packet
  have leftUnary : UnaryHistory leftMeet :=
    unary_cont_closed w0Unary d0Unary leftRoute
  have rightUnary : UnaryHistory rightMeet :=
    unary_cont_closed w1Unary d1Unary rightRoute
  have meetUnary : UnaryHistory meet :=
    unary_cont_closed leftUnary rightUnary meetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed meetUnary aUnary sealRoute
  exact
    ⟨leftUnary, rightUnary, meetUnary, sealUnary, hsame_refl sealRead, sealPkg⟩

end BEDC.Derived.RegularCauchyTailFiberUp

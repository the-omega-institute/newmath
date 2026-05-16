import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicToleranceTriangleLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicToleranceTriangleLedgerUp : Type where
  | mk :
      (Dm Dn Im In Em En M Q T H C P N : BHist) →
        DyadicToleranceTriangleLedgerUp

def dyadicToleranceTriangleLedgerEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicToleranceTriangleLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicToleranceTriangleLedgerEncodeBHist h

def dyadicToleranceTriangleLedgerDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicToleranceTriangleLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicToleranceTriangleLedgerDecodeBHist tail)

private theorem dyadicToleranceTriangleLedgerDecode_encode_bhist :
    ∀ h : BHist,
      dyadicToleranceTriangleLedgerDecodeBHist
          (dyadicToleranceTriangleLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicToleranceTriangleLedgerToEventFlow :
    DyadicToleranceTriangleLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DyadicToleranceTriangleLedgerUp.mk Dm Dn Im In Em En M Q T H C P N =>
      [[BMark.b1, BMark.b0, BMark.b1],
        dyadicToleranceTriangleLedgerEncodeBHist Dm,
        dyadicToleranceTriangleLedgerEncodeBHist Dn,
        dyadicToleranceTriangleLedgerEncodeBHist Im,
        dyadicToleranceTriangleLedgerEncodeBHist In,
        dyadicToleranceTriangleLedgerEncodeBHist Em,
        dyadicToleranceTriangleLedgerEncodeBHist En,
        dyadicToleranceTriangleLedgerEncodeBHist M,
        dyadicToleranceTriangleLedgerEncodeBHist Q,
        dyadicToleranceTriangleLedgerEncodeBHist T,
        dyadicToleranceTriangleLedgerEncodeBHist H,
        dyadicToleranceTriangleLedgerEncodeBHist C,
        dyadicToleranceTriangleLedgerEncodeBHist P,
        dyadicToleranceTriangleLedgerEncodeBHist N]

def dyadicToleranceTriangleLedgerFromEventFlow :
    EventFlow → Option DyadicToleranceTriangleLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | _tag :: Dm :: Dn :: Im :: In :: Em :: En :: M :: Q :: T :: H :: C :: P :: N :: [] =>
      some
        (DyadicToleranceTriangleLedgerUp.mk
          (dyadicToleranceTriangleLedgerDecodeBHist Dm)
          (dyadicToleranceTriangleLedgerDecodeBHist Dn)
          (dyadicToleranceTriangleLedgerDecodeBHist Im)
          (dyadicToleranceTriangleLedgerDecodeBHist In)
          (dyadicToleranceTriangleLedgerDecodeBHist Em)
          (dyadicToleranceTriangleLedgerDecodeBHist En)
          (dyadicToleranceTriangleLedgerDecodeBHist M)
          (dyadicToleranceTriangleLedgerDecodeBHist Q)
          (dyadicToleranceTriangleLedgerDecodeBHist T)
          (dyadicToleranceTriangleLedgerDecodeBHist H)
          (dyadicToleranceTriangleLedgerDecodeBHist C)
          (dyadicToleranceTriangleLedgerDecodeBHist P)
          (dyadicToleranceTriangleLedgerDecodeBHist N))
  | _ => none

def dyadicToleranceTriangleLedgerFields :
    DyadicToleranceTriangleLedgerUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DyadicToleranceTriangleLedgerUp.mk Dm Dn Im In Em En M Q T H C P N =>
      [Dm, Dn, Im, In, Em, En, M, Q, T, H, C, P, N]

private theorem dyadicToleranceTriangleLedger_round_trip :
    ∀ x : DyadicToleranceTriangleLedgerUp,
      dyadicToleranceTriangleLedgerFromEventFlow
          (dyadicToleranceTriangleLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Dm Dn Im In Em En M Q T H C P N =>
      simp only [dyadicToleranceTriangleLedgerToEventFlow,
        dyadicToleranceTriangleLedgerFromEventFlow,
        dyadicToleranceTriangleLedgerDecode_encode_bhist]

private theorem dyadicToleranceTriangleLedgerToEventFlow_injective
    {x y : DyadicToleranceTriangleLedgerUp} :
    dyadicToleranceTriangleLedgerToEventFlow x =
        dyadicToleranceTriangleLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          dyadicToleranceTriangleLedgerFromEventFlow
            (dyadicToleranceTriangleLedgerToEventFlow x) :=
        (dyadicToleranceTriangleLedger_round_trip x).symm
      _ =
          dyadicToleranceTriangleLedgerFromEventFlow
            (dyadicToleranceTriangleLedgerToEventFlow y) :=
        congrArg dyadicToleranceTriangleLedgerFromEventFlow hxy
      _ = some y := dyadicToleranceTriangleLedger_round_trip y
  exact Option.some.inj optionEq

instance dyadicToleranceTriangleLedgerBHistCarrier :
    BHistCarrier DyadicToleranceTriangleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicToleranceTriangleLedgerToEventFlow
  fromEventFlow := dyadicToleranceTriangleLedgerFromEventFlow

instance dyadicToleranceTriangleLedgerChapterTasteGate :
    ChapterTasteGate DyadicToleranceTriangleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicToleranceTriangleLedgerFromEventFlow
          (dyadicToleranceTriangleLedgerToEventFlow x) =
        some x
    exact dyadicToleranceTriangleLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicToleranceTriangleLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicToleranceTriangleLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicToleranceTriangleLedgerChapterTasteGate

instance dyadicToleranceTriangleLedgerFieldFaithful :
    FieldFaithful DyadicToleranceTriangleLedgerUp where
  fields := dyadicToleranceTriangleLedgerFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk Dm1 Dn1 Im1 In1 Em1 En1 M1 Q1 T1 H1 C1 P1 N1 =>
        cases y with
        | mk Dm2 Dn2 Im2 In2 Em2 En2 M2 Q2 T2 H2 C2 P2 N2 =>
            injection h with hDm t1
            injection t1 with hDn t2
            injection t2 with hIm t3
            injection t3 with hIn t4
            injection t4 with hEm t5
            injection t5 with hEn t6
            injection t6 with hM t7
            injection t7 with hQ t8
            injection t8 with hT t9
            injection t9 with hH t10
            injection t10 with hC t11
            injection t11 with hP t12
            injection t12 with hN _
            cases hDm
            cases hDn
            cases hIm
            cases hIn
            cases hEm
            cases hEn
            cases hM
            cases hQ
            cases hT
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance dyadicToleranceTriangleLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicToleranceTriangleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicToleranceTriangleLedgerUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DyadicToleranceTriangleLedgerUp.mk
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

end BEDC.Derived.DyadicToleranceTriangleLedgerUp

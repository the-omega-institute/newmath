import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PiecewiseLinearApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PiecewiseLinearApproximationUp : Type where
  | mk (I M E A D F T H C P N : BHist) : PiecewiseLinearApproximationUp
  deriving DecidableEq

def piecewiseLinearApproximationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: piecewiseLinearApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: piecewiseLinearApproximationEncodeBHist h

def piecewiseLinearApproximationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (piecewiseLinearApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (piecewiseLinearApproximationDecodeBHist tail)

private theorem PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def piecewiseLinearApproximationFields :
    PiecewiseLinearApproximationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PiecewiseLinearApproximationUp.mk I M E A D F T H C P N =>
      [I, M, E, A, D, F, T, H, C, P, N]

def piecewiseLinearApproximationToEventFlow :
    PiecewiseLinearApproximationUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (piecewiseLinearApproximationFields x).map piecewiseLinearApproximationEncodeBHist

private def piecewiseLinearApproximationEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      piecewiseLinearApproximationEventAtDefault index rest

def piecewiseLinearApproximationFromEventFlow
    (ef : EventFlow) : Option PiecewiseLinearApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PiecewiseLinearApproximationUp.mk
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 0 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 1 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 2 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 3 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 4 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 5 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 6 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 7 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 8 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 9 ef))
      (piecewiseLinearApproximationDecodeBHist
        (piecewiseLinearApproximationEventAtDefault 10 ef)))

private theorem PiecewiseLinearApproximationTasteGate_single_carrier_alignment_round_trip :
    forall x : PiecewiseLinearApproximationUp,
      piecewiseLinearApproximationFromEventFlow
        (piecewiseLinearApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M E A D F T H C P N =>
      change
        some
          (PiecewiseLinearApproximationUp.mk
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist I))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist M))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist E))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist A))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist D))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist F))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist T))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist H))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist C))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist P))
            (piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist N))) =
          some (PiecewiseLinearApproximationUp.mk I M E A D F T H C P N)
      rw [PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode I,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode M,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode E,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode A,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode D,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode F,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode T,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode H,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode C,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode P,
        PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode N]

private theorem PiecewiseLinearApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PiecewiseLinearApproximationUp} :
    piecewiseLinearApproximationToEventFlow x =
      piecewiseLinearApproximationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      piecewiseLinearApproximationFromEventFlow
          (piecewiseLinearApproximationToEventFlow x) =
        piecewiseLinearApproximationFromEventFlow
          (piecewiseLinearApproximationToEventFlow y) :=
    congrArg piecewiseLinearApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PiecewiseLinearApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PiecewiseLinearApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem PiecewiseLinearApproximationTasteGate_single_carrier_alignment_fields :
    forall x y : PiecewiseLinearApproximationUp,
      piecewiseLinearApproximationFields x =
        piecewiseLinearApproximationFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 M1 E1 A1 D1 F1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 M2 E2 A2 D2 F2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance piecewiseLinearApproximationBHistCarrier :
    BHistCarrier PiecewiseLinearApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := piecewiseLinearApproximationToEventFlow
  fromEventFlow := piecewiseLinearApproximationFromEventFlow

instance piecewiseLinearApproximationChapterTasteGate :
    ChapterTasteGate PiecewiseLinearApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      piecewiseLinearApproximationFromEventFlow
        (piecewiseLinearApproximationToEventFlow x) = some x
    exact PiecewiseLinearApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PiecewiseLinearApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance piecewiseLinearApproximationFieldFaithful :
    FieldFaithful PiecewiseLinearApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := piecewiseLinearApproximationFields
  field_faithful := PiecewiseLinearApproximationTasteGate_single_carrier_alignment_fields

instance piecewiseLinearApproximationNontrivial :
    Nontrivial PiecewiseLinearApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PiecewiseLinearApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PiecewiseLinearApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PiecewiseLinearApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  piecewiseLinearApproximationChapterTasteGate

theorem PiecewiseLinearApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PiecewiseLinearApproximationUp) ∧
      Nonempty (FieldFaithful PiecewiseLinearApproximationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial PiecewiseLinearApproximationUp) ∧
          (forall h : BHist,
            piecewiseLinearApproximationDecodeBHist
              (piecewiseLinearApproximationEncodeBHist h) = h) ∧
            (forall x : PiecewiseLinearApproximationUp,
              piecewiseLinearApproximationFromEventFlow
                (piecewiseLinearApproximationToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨piecewiseLinearApproximationChapterTasteGate⟩,
      ⟨piecewiseLinearApproximationFieldFaithful⟩,
      ⟨piecewiseLinearApproximationNontrivial⟩,
      PiecewiseLinearApproximationTasteGate_single_carrier_alignment_decode,
      PiecewiseLinearApproximationTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.PiecewiseLinearApproximationUp

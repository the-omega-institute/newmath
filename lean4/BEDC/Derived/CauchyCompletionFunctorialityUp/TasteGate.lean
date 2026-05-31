import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionFunctorialityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionFunctorialityUp : Type where
  | mk (S T f E U I L H C P N : BHist) : CauchyCompletionFunctorialityUp
  deriving DecidableEq

def cauchyCompletionFunctorialityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionFunctorialityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionFunctorialityEncodeBHist h

def cauchyCompletionFunctorialityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionFunctorialityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionFunctorialityDecodeBHist tail)

private theorem CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionFunctorialityFields :
    CauchyCompletionFunctorialityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionFunctorialityUp.mk S T f E U I L H C P N =>
      [S, T, f, E, U, I, L, H, C, P, N]

def cauchyCompletionFunctorialityToEventFlow :
    CauchyCompletionFunctorialityUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionFunctorialityFields x).map
      cauchyCompletionFunctorialityEncodeBHist

private def cauchyCompletionFunctorialityEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionFunctorialityEventAtDefault index rest

def cauchyCompletionFunctorialityFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionFunctorialityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionFunctorialityUp.mk
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 0 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 1 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 2 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 3 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 4 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 5 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 6 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 7 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 8 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 9 ef))
      (cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEventAtDefault 10 ef)))

private theorem CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyCompletionFunctorialityUp,
      cauchyCompletionFunctorialityFromEventFlow
        (cauchyCompletionFunctorialityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S T f E U I L H C P N =>
      change
        some
          (CauchyCompletionFunctorialityUp.mk
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist S))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist T))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist f))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist E))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist U))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist I))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist L))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist H))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist C))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist P))
            (cauchyCompletionFunctorialityDecodeBHist
              (cauchyCompletionFunctorialityEncodeBHist N))) =
          some (CauchyCompletionFunctorialityUp.mk S T f E U I L H C P N)
      rw [CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode T,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode f,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode U,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode I,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode L,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionFunctorialityUp} :
    cauchyCompletionFunctorialityToEventFlow x =
        cauchyCompletionFunctorialityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionFunctorialityFromEventFlow
          (cauchyCompletionFunctorialityToEventFlow x) =
        cauchyCompletionFunctorialityFromEventFlow
          (cauchyCompletionFunctorialityToEventFlow y) :=
    congrArg cauchyCompletionFunctorialityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_fields :
    forall x y : CauchyCompletionFunctorialityUp,
      cauchyCompletionFunctorialityFields x =
          cauchyCompletionFunctorialityFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 f1 E1 U1 I1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 f2 E2 U2 I2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletionFunctorialityBHistCarrier :
    BHistCarrier CauchyCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionFunctorialityToEventFlow
  fromEventFlow := cauchyCompletionFunctorialityFromEventFlow

instance cauchyCompletionFunctorialityChapterTasteGate :
    ChapterTasteGate CauchyCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionFunctorialityFromEventFlow
        (cauchyCompletionFunctorialityToEventFlow x) = some x
    exact CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance cauchyCompletionFunctorialityFieldFaithful :
    FieldFaithful CauchyCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionFunctorialityFields
  field_faithful :=
    CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_fields

instance cauchyCompletionFunctorialityNontrivial :
    Nontrivial CauchyCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionFunctorialityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionFunctorialityUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionFunctorialityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionFunctorialityChapterTasteGate

theorem CauchyCompletionFunctorialityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyCompletionFunctorialityDecodeBHist
        (cauchyCompletionFunctorialityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionFunctorialityUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionFunctorialityUp) ∧
          cauchyCompletionFunctorialityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨CauchyCompletionFunctorialityTasteGate_single_carrier_alignment_decode,
      ⟨cauchyCompletionFunctorialityBHistCarrier⟩,
      ⟨cauchyCompletionFunctorialityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionFunctorialityUp

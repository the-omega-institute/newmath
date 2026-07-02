import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopEquicontinuityPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopEquicontinuityPrincipleUp : Type where
  | mk (F I M U W R D S H C P N : BHist) : BishopEquicontinuityPrincipleUp
  deriving DecidableEq

def bishopEquicontinuityPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopEquicontinuityPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopEquicontinuityPrincipleEncodeBHist h

def bishopEquicontinuityPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopEquicontinuityPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopEquicontinuityPrincipleDecodeBHist tail)

private theorem BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopEquicontinuityPrincipleFields :
    BishopEquicontinuityPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopEquicontinuityPrincipleUp.mk F I M U W R D S H C P N =>
      [F, I, M, U, W, R, D, S, H, C, P, N]

def bishopEquicontinuityPrincipleToEventFlow :
    BishopEquicontinuityPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopEquicontinuityPrincipleFields x).map
        bishopEquicontinuityPrincipleEncodeBHist

private def bishopEquicontinuityPrincipleEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopEquicontinuityPrincipleEventAtDefault index rest

def bishopEquicontinuityPrincipleFromEventFlow
    (ef : EventFlow) : Option BishopEquicontinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopEquicontinuityPrincipleUp.mk
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 0 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 1 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 2 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 3 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 4 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 5 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 6 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 7 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 8 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 9 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 10 ef))
      (bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEventAtDefault 11 ef)))

private theorem BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopEquicontinuityPrincipleUp,
      bishopEquicontinuityPrincipleFromEventFlow
        (bishopEquicontinuityPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I M U W R D S H C P N =>
      change
        some
          (BishopEquicontinuityPrincipleUp.mk
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist F))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist I))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist M))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist U))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist W))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist R))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist D))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist S))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist H))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist C))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist P))
            (bishopEquicontinuityPrincipleDecodeBHist
              (bishopEquicontinuityPrincipleEncodeBHist N))) =
          some (BishopEquicontinuityPrincipleUp.mk F I M U W R D S H C P N)
      rw [BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode F,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode I,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode M,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode U,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode W,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode R,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode D,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode S,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode H,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode C,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode P,
        BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode N]

private theorem BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_injective
    {x y : BishopEquicontinuityPrincipleUp} :
    bishopEquicontinuityPrincipleToEventFlow x =
      bishopEquicontinuityPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopEquicontinuityPrincipleFromEventFlow
          (bishopEquicontinuityPrincipleToEventFlow x) =
        bishopEquicontinuityPrincipleFromEventFlow
          (bishopEquicontinuityPrincipleToEventFlow y) :=
    congrArg bishopEquicontinuityPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopEquicontinuityPrincipleUp,
      bishopEquicontinuityPrincipleFields x = bishopEquicontinuityPrincipleFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 I1 M1 U1 W1 R1 D1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 I2 M2 U2 W2 R2 D2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopEquicontinuityPrincipleBHistCarrier :
    BHistCarrier BishopEquicontinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopEquicontinuityPrincipleToEventFlow
  fromEventFlow := bishopEquicontinuityPrincipleFromEventFlow

instance bishopEquicontinuityPrincipleChapterTasteGate :
    ChapterTasteGate BishopEquicontinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopEquicontinuityPrincipleFromEventFlow
        (bishopEquicontinuityPrincipleToEventFlow x) = some x
    exact BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_injective heq)

instance bishopEquicontinuityPrincipleFieldFaithful :
    FieldFaithful BishopEquicontinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopEquicontinuityPrincipleFields
  field_faithful := BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_fields

instance bishopEquicontinuityPrincipleNontrivial :
    Nontrivial BishopEquicontinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopEquicontinuityPrincipleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BishopEquicontinuityPrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopEquicontinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopEquicontinuityPrincipleChapterTasteGate

theorem BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopEquicontinuityPrincipleDecodeBHist
        (bishopEquicontinuityPrincipleEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopEquicontinuityPrincipleUp) ∧
        Nonempty (ChapterTasteGate BishopEquicontinuityPrincipleUp) ∧
          Nonempty (FieldFaithful BishopEquicontinuityPrincipleUp) ∧
            bishopEquicontinuityPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BishopEquicontinuityPrincipleTasteGate_single_carrier_alignment_decode,
      ⟨bishopEquicontinuityPrincipleBHistCarrier⟩,
      ⟨bishopEquicontinuityPrincipleChapterTasteGate⟩,
      ⟨bishopEquicontinuityPrincipleFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.BishopEquicontinuityPrincipleUp

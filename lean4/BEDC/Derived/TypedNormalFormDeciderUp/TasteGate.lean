import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypedNormalFormDeciderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypedNormalFormDeciderUp : Type where
  | mk (I L R TL TR F NL NR E W Q H C P A : BHist) : TypedNormalFormDeciderUp
  deriving DecidableEq

def typedNormalFormDeciderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typedNormalFormDeciderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typedNormalFormDeciderEncodeBHist h

def typedNormalFormDeciderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typedNormalFormDeciderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typedNormalFormDeciderDecodeBHist tail)

private theorem TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def typedNormalFormDeciderFields : TypedNormalFormDeciderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypedNormalFormDeciderUp.mk I L R TL TR F NL NR E W Q H C P A =>
      [I, L, R, TL, TR, F, NL, NR, E, W, Q, H, C, P, A]

def typedNormalFormDeciderToEventFlow : TypedNormalFormDeciderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (typedNormalFormDeciderFields x).map typedNormalFormDeciderEncodeBHist

private def typedNormalFormDeciderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => typedNormalFormDeciderEventAtDefault index rest

def typedNormalFormDeciderFromEventFlow :
    EventFlow → Option TypedNormalFormDeciderUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (TypedNormalFormDeciderUp.mk
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 0 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 1 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 2 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 3 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 4 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 5 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 6 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 7 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 8 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 9 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 10 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 11 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 12 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 13 ef))
          (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEventAtDefault 14 ef)))

private theorem TypedNormalFormDeciderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TypedNormalFormDeciderUp,
      typedNormalFormDeciderFromEventFlow (typedNormalFormDeciderToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L R TL TR F NL NR E W Q H C P A =>
      change
        some
          (TypedNormalFormDeciderUp.mk
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist I))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist L))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist R))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist TL))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist TR))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist F))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist NL))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist NR))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist E))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist W))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist Q))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist H))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist C))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist P))
            (typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist A))) =
          some (TypedNormalFormDeciderUp.mk I L R TL TR F NL NR E W Q H C P A)
      rw [TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode I,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode L,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode R,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode TL,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode TR,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode F,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode NL,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode NR,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode E,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode W,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode Q,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode H,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode C,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode P,
        TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode A]

private theorem TypedNormalFormDeciderTasteGate_single_carrier_alignment_injective
    {x y : TypedNormalFormDeciderUp} :
    typedNormalFormDeciderToEventFlow x = typedNormalFormDeciderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typedNormalFormDeciderFromEventFlow (typedNormalFormDeciderToEventFlow x) =
        typedNormalFormDeciderFromEventFlow (typedNormalFormDeciderToEventFlow y) :=
    congrArg typedNormalFormDeciderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TypedNormalFormDeciderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TypedNormalFormDeciderTasteGate_single_carrier_alignment_round_trip y)))

private theorem TypedNormalFormDeciderTasteGate_single_carrier_alignment_fields :
    ∀ x y : TypedNormalFormDeciderUp,
      typedNormalFormDeciderFields x = typedNormalFormDeciderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 L1 R1 TL1 TR1 F1 NL1 NR1 E1 W1 Q1 H1 C1 P1 A1 =>
      cases y with
      | mk I2 L2 R2 TL2 TR2 F2 NL2 NR2 E2 W2 Q2 H2 C2 P2 A2 =>
          cases hfields
          rfl

instance typedNormalFormDeciderBHistCarrier :
    BHistCarrier TypedNormalFormDeciderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typedNormalFormDeciderToEventFlow
  fromEventFlow := typedNormalFormDeciderFromEventFlow

instance typedNormalFormDeciderChapterTasteGate :
    ChapterTasteGate TypedNormalFormDeciderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change typedNormalFormDeciderFromEventFlow (typedNormalFormDeciderToEventFlow x) =
      some x
    exact TypedNormalFormDeciderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TypedNormalFormDeciderTasteGate_single_carrier_alignment_injective heq)

instance typedNormalFormDeciderFieldFaithful :
    FieldFaithful TypedNormalFormDeciderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := typedNormalFormDeciderFields
  field_faithful := TypedNormalFormDeciderTasteGate_single_carrier_alignment_fields

instance typedNormalFormDeciderNontrivial :
    Nontrivial TypedNormalFormDeciderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypedNormalFormDeciderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypedNormalFormDeciderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TypedNormalFormDeciderTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier TypedNormalFormDeciderUp) ∧
      Nonempty (ChapterTasteGate TypedNormalFormDeciderUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial TypedNormalFormDeciderUp) ∧
          (∀ h : BHist,
            typedNormalFormDeciderDecodeBHist (typedNormalFormDeciderEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨typedNormalFormDeciderBHistCarrier⟩,
      ⟨typedNormalFormDeciderChapterTasteGate⟩,
      ⟨typedNormalFormDeciderNontrivial⟩,
      TypedNormalFormDeciderTasteGate_single_carrier_alignment_decode⟩

end BEDC.Derived.TypedNormalFormDeciderUp

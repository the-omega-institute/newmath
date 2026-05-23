import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KreiselLacombeShoenfieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KreiselLacombeShoenfieldUp : Type where
  | mk (B O S R E M L H C P N : BHist) : KreiselLacombeShoenfieldUp
  deriving DecidableEq

def kreiselLacombeShoenfieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kreiselLacombeShoenfieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kreiselLacombeShoenfieldEncodeBHist h

def kreiselLacombeShoenfieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kreiselLacombeShoenfieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kreiselLacombeShoenfieldDecodeBHist tail)

private theorem KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kreiselLacombeShoenfieldFields : KreiselLacombeShoenfieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KreiselLacombeShoenfieldUp.mk B O S R E M L H C P N =>
      [B, O, S, R, E, M, L, H, C, P, N]

def kreiselLacombeShoenfieldToEventFlow :
    KreiselLacombeShoenfieldUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (kreiselLacombeShoenfieldFields x).map kreiselLacombeShoenfieldEncodeBHist

private def kreiselLacombeShoenfieldEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kreiselLacombeShoenfieldEventAtDefault index rest

def kreiselLacombeShoenfieldFromEventFlow
    (ef : EventFlow) : Option KreiselLacombeShoenfieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KreiselLacombeShoenfieldUp.mk
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 0 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 1 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 2 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 3 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 4 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 5 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 6 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 7 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 8 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 9 ef))
      (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAtDefault 10 ef)))

private theorem KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KreiselLacombeShoenfieldUp,
      kreiselLacombeShoenfieldFromEventFlow (kreiselLacombeShoenfieldToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk B O S R E M L H C P N =>
      change
        some
          (KreiselLacombeShoenfieldUp.mk
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist B))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist O))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist S))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist R))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist E))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist M))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist L))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist H))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist C))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist P))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist N))) =
          some (KreiselLacombeShoenfieldUp.mk B O S R E M L H C P N)
      rw [KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode B,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode O,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode S,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode R,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode E,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode M,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode L,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode H,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode C,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode P,
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode N]

private theorem KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KreiselLacombeShoenfieldUp} :
    kreiselLacombeShoenfieldToEventFlow x = kreiselLacombeShoenfieldToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kreiselLacombeShoenfieldFromEventFlow (kreiselLacombeShoenfieldToEventFlow x) =
        kreiselLacombeShoenfieldFromEventFlow (kreiselLacombeShoenfieldToEventFlow y) :=
    congrArg kreiselLacombeShoenfieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : KreiselLacombeShoenfieldUp,
      kreiselLacombeShoenfieldFields x = kreiselLacombeShoenfieldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 O1 S1 R1 E1 M1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 O2 S2 R2 E2 M2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance kreiselLacombeShoenfieldBHistCarrier :
    BHistCarrier KreiselLacombeShoenfieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kreiselLacombeShoenfieldToEventFlow
  fromEventFlow := kreiselLacombeShoenfieldFromEventFlow

instance kreiselLacombeShoenfieldChapterTasteGate :
    ChapterTasteGate KreiselLacombeShoenfieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kreiselLacombeShoenfieldFromEventFlow
        (kreiselLacombeShoenfieldToEventFlow x) = some x
    exact KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kreiselLacombeShoenfieldFieldFaithful :
    FieldFaithful KreiselLacombeShoenfieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kreiselLacombeShoenfieldFields
  field_faithful := KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_fields

instance kreiselLacombeShoenfieldNontrivial :
    Nontrivial KreiselLacombeShoenfieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KreiselLacombeShoenfieldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KreiselLacombeShoenfieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KreiselLacombeShoenfieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kreiselLacombeShoenfieldChapterTasteGate

theorem KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEncodeBHist h) =
        h) ∧
      (∀ x : KreiselLacombeShoenfieldUp,
        kreiselLacombeShoenfieldFromEventFlow (kreiselLacombeShoenfieldToEventFlow x) =
          some x) ∧
        (∀ x y : KreiselLacombeShoenfieldUp,
          kreiselLacombeShoenfieldToEventFlow x =
            kreiselLacombeShoenfieldToEventFlow y → x = y) ∧
          kreiselLacombeShoenfieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_decode,
      KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KreiselLacombeShoenfieldUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KreiselLacombeShoenfieldUp

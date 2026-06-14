import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicBusemannCocycleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicBusemannCocycleUp : Type where
  | mk (M Xi R0 R1 G V Q E H K P N : BHist) : HyperbolicBusemannCocycleUp
  deriving DecidableEq

def hyperbolicBusemannCocycleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicBusemannCocycleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicBusemannCocycleEncodeBHist h

def hyperbolicBusemannCocycleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicBusemannCocycleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicBusemannCocycleDecodeBHist tail)

private theorem HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hyperbolicBusemannCocycleDecodeBHist
      (hyperbolicBusemannCocycleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicBusemannCocycleFields : HyperbolicBusemannCocycleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicBusemannCocycleUp.mk M Xi R0 R1 G V Q E H K P N =>
      [M, Xi, R0, R1, G, V, Q, E, H, K, P, N]

def hyperbolicBusemannCocycleToEventFlow : HyperbolicBusemannCocycleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicBusemannCocycleFields x).map hyperbolicBusemannCocycleEncodeBHist

private def hyperbolicBusemannCocycleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicBusemannCocycleEventAtDefault index rest

def hyperbolicBusemannCocycleFromEventFlow
    (ef : EventFlow) : Option HyperbolicBusemannCocycleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicBusemannCocycleUp.mk
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 0 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 1 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 2 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 3 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 4 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 5 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 6 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 7 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 8 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 9 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 10 ef))
      (hyperbolicBusemannCocycleDecodeBHist
        (hyperbolicBusemannCocycleEventAtDefault 11 ef)))

private theorem HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicBusemannCocycleUp) :
    hyperbolicBusemannCocycleFromEventFlow
      (hyperbolicBusemannCocycleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M Xi R0 R1 G V Q E H K P N =>
      change
        some
          (HyperbolicBusemannCocycleUp.mk
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist M))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist Xi))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist R0))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist R1))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist G))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist V))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist Q))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist E))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist H))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist K))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist P))
            (hyperbolicBusemannCocycleDecodeBHist
              (hyperbolicBusemannCocycleEncodeBHist N))) =
          some (HyperbolicBusemannCocycleUp.mk M Xi R0 R1 G V Q E H K P N)
      rw [HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode M,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode Xi,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode R0,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode R1,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode G,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode V,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode Q,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode E,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode H,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode K,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode P,
        HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicBusemannCocycleUp} :
    hyperbolicBusemannCocycleToEventFlow x =
      hyperbolicBusemannCocycleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicBusemannCocycleFromEventFlow
          (hyperbolicBusemannCocycleToEventFlow x) =
        hyperbolicBusemannCocycleFromEventFlow
          (hyperbolicBusemannCocycleToEventFlow y) :=
    congrArg hyperbolicBusemannCocycleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : HyperbolicBusemannCocycleUp,
      hyperbolicBusemannCocycleFields x = hyperbolicBusemannCocycleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 Xi1 R01 R11 G1 V1 Q1 E1 H1 K1 P1 N1 =>
      cases y with
      | mk M2 Xi2 R02 R12 G2 V2 Q2 E2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicBusemannCocycleBHistCarrier :
    BHistCarrier HyperbolicBusemannCocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicBusemannCocycleToEventFlow
  fromEventFlow := hyperbolicBusemannCocycleFromEventFlow

instance hyperbolicBusemannCocycleChapterTasteGate :
    ChapterTasteGate HyperbolicBusemannCocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperbolicBusemannCocycleFromEventFlow
      (hyperbolicBusemannCocycleToEventFlow x) = some x
    exact HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hyperbolicBusemannCocycleFieldFaithful :
    FieldFaithful HyperbolicBusemannCocycleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicBusemannCocycleFields
  field_faithful :=
    HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_fields_faithful

theorem HyperbolicBusemannCocycleTasteGate_single_carrier_alignment :
    (∀ h : BHist, hyperbolicBusemannCocycleDecodeBHist
      (hyperbolicBusemannCocycleEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HyperbolicBusemannCocycleUp) ∧
        Nonempty (ChapterTasteGate HyperbolicBusemannCocycleUp) ∧
          hyperbolicBusemannCocycleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HyperbolicBusemannCocycleTasteGate_single_carrier_alignment_decode_encode,
      ⟨hyperbolicBusemannCocycleBHistCarrier⟩,
      ⟨hyperbolicBusemannCocycleChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HyperbolicBusemannCocycleUp

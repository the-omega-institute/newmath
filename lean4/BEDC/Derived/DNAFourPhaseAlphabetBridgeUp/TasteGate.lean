import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DNAFourPhaseAlphabetBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DNAFourPhaseAlphabetBridgeUp : Type where
  | mk (B Q A E H C P N : BHist) : DNAFourPhaseAlphabetBridgeUp
  deriving DecidableEq

def dnaFourPhaseAlphabetBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dnaFourPhaseAlphabetBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dnaFourPhaseAlphabetBridgeEncodeBHist h

def dnaFourPhaseAlphabetBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dnaFourPhaseAlphabetBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dnaFourPhaseAlphabetBridgeDecodeBHist tail)

private theorem dnaFourPhaseAlphabetBridgeDecodeEncodeBHist :
    ∀ h : BHist,
      dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dnaFourPhaseAlphabetBridgeFields : DNAFourPhaseAlphabetBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DNAFourPhaseAlphabetBridgeUp.mk B Q A E H C P N => [B, Q, A, E, H, C, P, N]

def dnaFourPhaseAlphabetBridgeToEventFlow : DNAFourPhaseAlphabetBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dnaFourPhaseAlphabetBridgeFields x).map dnaFourPhaseAlphabetBridgeEncodeBHist

private def dnaFourPhaseAlphabetBridgeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dnaFourPhaseAlphabetBridgeEventAt index rest

def dnaFourPhaseAlphabetBridgeFromEventFlow (ef : EventFlow) :
    Option DNAFourPhaseAlphabetBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DNAFourPhaseAlphabetBridgeUp.mk
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 0 ef))
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 1 ef))
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 2 ef))
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 3 ef))
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 4 ef))
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 5 ef))
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 6 ef))
      (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEventAt 7 ef)))

private theorem dnaFourPhaseAlphabetBridge_round_trip
    (x : DNAFourPhaseAlphabetBridgeUp) :
    dnaFourPhaseAlphabetBridgeFromEventFlow
      (dnaFourPhaseAlphabetBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B Q A E H C P N =>
      change
        some
          (DNAFourPhaseAlphabetBridgeUp.mk
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist B))
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist Q))
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist A))
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist E))
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist H))
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist C))
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist P))
            (dnaFourPhaseAlphabetBridgeDecodeBHist (dnaFourPhaseAlphabetBridgeEncodeBHist N))) =
          some (DNAFourPhaseAlphabetBridgeUp.mk B Q A E H C P N)
      rw [dnaFourPhaseAlphabetBridgeDecodeEncodeBHist B,
        dnaFourPhaseAlphabetBridgeDecodeEncodeBHist Q,
        dnaFourPhaseAlphabetBridgeDecodeEncodeBHist A,
        dnaFourPhaseAlphabetBridgeDecodeEncodeBHist E,
        dnaFourPhaseAlphabetBridgeDecodeEncodeBHist H,
        dnaFourPhaseAlphabetBridgeDecodeEncodeBHist C,
        dnaFourPhaseAlphabetBridgeDecodeEncodeBHist P,
        dnaFourPhaseAlphabetBridgeDecodeEncodeBHist N]

private theorem dnaFourPhaseAlphabetBridgeToEventFlow_injective
    {x y : DNAFourPhaseAlphabetBridgeUp} :
    dnaFourPhaseAlphabetBridgeToEventFlow x = dnaFourPhaseAlphabetBridgeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dnaFourPhaseAlphabetBridgeFromEventFlow (dnaFourPhaseAlphabetBridgeToEventFlow x) =
        dnaFourPhaseAlphabetBridgeFromEventFlow (dnaFourPhaseAlphabetBridgeToEventFlow y) :=
    congrArg dnaFourPhaseAlphabetBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dnaFourPhaseAlphabetBridge_round_trip x).symm
      (Eq.trans hread (dnaFourPhaseAlphabetBridge_round_trip y)))

private theorem dnaFourPhaseAlphabetBridge_fields_faithful :
    ∀ x y : DNAFourPhaseAlphabetBridgeUp,
      dnaFourPhaseAlphabetBridgeFields x = dnaFourPhaseAlphabetBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ Q₁ A₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ Q₂ A₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dnaFourPhaseAlphabetBridgeBHistCarrier :
    BHistCarrier DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dnaFourPhaseAlphabetBridgeToEventFlow
  fromEventFlow := dnaFourPhaseAlphabetBridgeFromEventFlow

instance dnaFourPhaseAlphabetBridgeChapterTasteGate :
    ChapterTasteGate DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dnaFourPhaseAlphabetBridgeFromEventFlow (dnaFourPhaseAlphabetBridgeToEventFlow x) =
        some x
    exact dnaFourPhaseAlphabetBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dnaFourPhaseAlphabetBridgeToEventFlow_injective heq)

instance dnaFourPhaseAlphabetBridgeFieldFaithful :
    FieldFaithful DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dnaFourPhaseAlphabetBridgeFields
  field_faithful := dnaFourPhaseAlphabetBridge_fields_faithful

instance dnaFourPhaseAlphabetBridgeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DNAFourPhaseAlphabetBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DNAFourPhaseAlphabetBridgeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DNAFourPhaseAlphabetBridgeUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DNAFourPhaseAlphabetBridgeUp) ∧
      Nonempty (FieldFaithful DNAFourPhaseAlphabetBridgeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DNAFourPhaseAlphabetBridgeUp) ∧
          (∀ h : BHist,
            dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist h) = h) ∧
            (∀ x : DNAFourPhaseAlphabetBridgeUp,
              dnaFourPhaseAlphabetBridgeFromEventFlow
                (dnaFourPhaseAlphabetBridgeToEventFlow x) = some x) ∧
              (∀ x y : DNAFourPhaseAlphabetBridgeUp,
                dnaFourPhaseAlphabetBridgeToEventFlow x =
                  dnaFourPhaseAlphabetBridgeToEventFlow y → x = y) ∧
                dnaFourPhaseAlphabetBridgeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨dnaFourPhaseAlphabetBridgeChapterTasteGate⟩,
      ⟨dnaFourPhaseAlphabetBridgeFieldFaithful⟩,
      ⟨dnaFourPhaseAlphabetBridgeNontrivial⟩,
      dnaFourPhaseAlphabetBridgeDecodeEncodeBHist,
      dnaFourPhaseAlphabetBridge_round_trip,
      (fun _ _ heq => dnaFourPhaseAlphabetBridgeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DNAFourPhaseAlphabetBridgeUp

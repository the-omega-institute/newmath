import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BisectionConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BisectionConvergenceUp : Type where
  | mk : (I D W T S Q E H C P N : BHist) → BisectionConvergenceUp
  deriving DecidableEq

def bisectionConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bisectionConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bisectionConvergenceEncodeBHist h

def bisectionConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bisectionConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bisectionConvergenceDecodeBHist tail)

def bisectionConvergenceReadBHist : EventFlow → Nat → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => BHist.Empty
  | raw :: _, 0 => bisectionConvergenceDecodeBHist raw
  | _ :: rest, Nat.succ n => bisectionConvergenceReadBHist rest n

private theorem BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bisectionConvergenceFields : BisectionConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BisectionConvergenceUp.mk I D W T S Q E H C P N => [I, D, W, T, S, Q, E, H, C, P, N]

def bisectionConvergenceToEventFlow : BisectionConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bisectionConvergenceFields x).map bisectionConvergenceEncodeBHist

def bisectionConvergenceFromEventFlow : EventFlow → Option BisectionConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BisectionConvergenceUp.mk
          (bisectionConvergenceReadBHist ef 0)
          (bisectionConvergenceReadBHist ef 1)
          (bisectionConvergenceReadBHist ef 2)
          (bisectionConvergenceReadBHist ef 3)
          (bisectionConvergenceReadBHist ef 4)
          (bisectionConvergenceReadBHist ef 5)
          (bisectionConvergenceReadBHist ef 6)
          (bisectionConvergenceReadBHist ef 7)
          (bisectionConvergenceReadBHist ef 8)
          (bisectionConvergenceReadBHist ef 9)
          (bisectionConvergenceReadBHist ef 10))

private theorem BisectionConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BisectionConvergenceUp,
      bisectionConvergenceFromEventFlow (bisectionConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D W T S Q E H C P N =>
      change
        some
          (BisectionConvergenceUp.mk
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist I))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist D))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist W))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist T))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist S))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist Q))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist E))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist H))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist C))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist P))
            (bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist N))) =
          some (BisectionConvergenceUp.mk I D W T S Q E H C P N)
      rw [BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode I,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode D,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode T,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode S,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode Q,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BisectionConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BisectionConvergenceUp} :
    bisectionConvergenceToEventFlow x = bisectionConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bisectionConvergenceFromEventFlow (bisectionConvergenceToEventFlow x) =
        bisectionConvergenceFromEventFlow (bisectionConvergenceToEventFlow y) :=
    congrArg bisectionConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BisectionConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BisectionConvergenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BisectionConvergenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BisectionConvergenceUp, bisectionConvergenceFields x =
      bisectionConvergenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ D₁ W₁ T₁ S₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ D₂ W₂ T₂ S₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hI tail0
          injection tail0 with hD tail1
          injection tail1 with hW tail2
          injection tail2 with hT tail3
          injection tail3 with hS tail4
          injection tail4 with hQ tail5
          injection tail5 with hE tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hI
          subst hD
          subst hW
          subst hT
          subst hS
          subst hQ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance bisectionConvergenceBHistCarrier : BHistCarrier BisectionConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bisectionConvergenceToEventFlow
  fromEventFlow := bisectionConvergenceFromEventFlow

instance bisectionConvergenceChapterTasteGate : ChapterTasteGate BisectionConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bisectionConvergenceFromEventFlow (bisectionConvergenceToEventFlow x) = some x
    exact BisectionConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BisectionConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bisectionConvergenceFieldFaithful : FieldFaithful BisectionConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bisectionConvergenceFields
  field_faithful := BisectionConvergenceTasteGate_single_carrier_alignment_fields_faithful

instance bisectionConvergenceNontrivial : Nontrivial BisectionConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BisectionConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BisectionConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BisectionConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, bisectionConvergenceDecodeBHist (bisectionConvergenceEncodeBHist h) = h) ∧
      (∀ x : BisectionConvergenceUp,
        bisectionConvergenceFromEventFlow (bisectionConvergenceToEventFlow x) = some x) ∧
        (∀ x y : BisectionConvergenceUp,
          bisectionConvergenceToEventFlow x = bisectionConvergenceToEventFlow y → x = y) ∧
          bisectionConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BisectionConvergenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact BisectionConvergenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BisectionConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.BisectionConvergenceUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCompletionUp : Type where
  | mk (S Q D K E H C P N : BHist) : SequentialCompletionUp
  deriving DecidableEq

def sequentialCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCompletionEncodeBHist h

def sequentialCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCompletionDecodeBHist tail)

private theorem SequentialCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentialCompletionFields : SequentialCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCompletionUp.mk S Q D K E H C P N => [S, Q, D, K, E, H, C, P, N]

def sequentialCompletionToEventFlow : SequentialCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialCompletionFields x).map sequentialCompletionEncodeBHist

def sequentialCompletionFromEventFlow : EventFlow → Option SequentialCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: Q :: D :: K :: E :: H :: C :: P :: N :: [] =>
      some
        (SequentialCompletionUp.mk
          (sequentialCompletionDecodeBHist S)
          (sequentialCompletionDecodeBHist Q)
          (sequentialCompletionDecodeBHist D)
          (sequentialCompletionDecodeBHist K)
          (sequentialCompletionDecodeBHist E)
          (sequentialCompletionDecodeBHist H)
          (sequentialCompletionDecodeBHist C)
          (sequentialCompletionDecodeBHist P)
          (sequentialCompletionDecodeBHist N))
  | _ => none

private theorem sequentialCompletion_round_trip :
    ∀ x : SequentialCompletionUp,
      sequentialCompletionFromEventFlow (sequentialCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D K E H C P N =>
      change
        some
          (SequentialCompletionUp.mk
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist S))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist Q))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist D))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist K))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist E))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist H))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist C))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist P))
            (sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist N))) =
          some (SequentialCompletionUp.mk S Q D K E H C P N)
      rw [SequentialCompletionTasteGate_single_carrier_alignment_decode_encode S,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode D,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode K,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode E,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode H,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode C,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode P,
        SequentialCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem sequentialCompletionToEventFlow_injective {x y : SequentialCompletionUp} :
    sequentialCompletionToEventFlow x = sequentialCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCompletionFromEventFlow (sequentialCompletionToEventFlow x) =
        sequentialCompletionFromEventFlow (sequentialCompletionToEventFlow y) :=
    congrArg sequentialCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentialCompletion_round_trip x).symm
      (Eq.trans hread (sequentialCompletion_round_trip y)))

private theorem SequentialCompletionTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    sequentialCompletionEncodeBHist h = sequentialCompletionEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  calc
    h = sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist h) :=
      (SequentialCompletionTasteGate_single_carrier_alignment_decode_encode h).symm
    _ = sequentialCompletionDecodeBHist (sequentialCompletionEncodeBHist k) :=
      congrArg sequentialCompletionDecodeBHist heq
    _ = k := SequentialCompletionTasteGate_single_carrier_alignment_decode_encode k

private theorem SequentialCompletionTasteGate_single_carrier_alignment_direct
    {x y : SequentialCompletionUp} :
    sequentialCompletionToEventFlow x = sequentialCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S₁ Q₁ D₁ K₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ D₂ K₂ E₂ H₂ C₂ P₂ N₂ =>
          change
            [sequentialCompletionEncodeBHist S₁, sequentialCompletionEncodeBHist Q₁,
              sequentialCompletionEncodeBHist D₁, sequentialCompletionEncodeBHist K₁,
              sequentialCompletionEncodeBHist E₁, sequentialCompletionEncodeBHist H₁,
              sequentialCompletionEncodeBHist C₁, sequentialCompletionEncodeBHist P₁,
              sequentialCompletionEncodeBHist N₁] =
              [sequentialCompletionEncodeBHist S₂, sequentialCompletionEncodeBHist Q₂,
                sequentialCompletionEncodeBHist D₂, sequentialCompletionEncodeBHist K₂,
                sequentialCompletionEncodeBHist E₂, sequentialCompletionEncodeBHist H₂,
                sequentialCompletionEncodeBHist C₂, sequentialCompletionEncodeBHist P₂,
                sequentialCompletionEncodeBHist N₂] at heq
          injection heq with hS tail0
          injection tail0 with hQ tail1
          injection tail1 with hD tail2
          injection tail2 with hK tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          have hs := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hS
          have hq := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hQ
          have hd := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hD
          have hk := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hK
          have he := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hE
          have hh := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hH
          have hc := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hC
          have hp := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hP
          have hn := SequentialCompletionTasteGate_single_carrier_alignment_encode_injective hN
          subst hs
          subst hq
          subst hd
          subst hk
          subst he
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance sequentialCompletionBHistCarrier :
    BHistCarrier SequentialCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCompletionToEventFlow
  fromEventFlow := sequentialCompletionFromEventFlow

instance sequentialCompletionChapterTasteGate :
    ChapterTasteGate SequentialCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialCompletionFromEventFlow (sequentialCompletionToEventFlow x) = some x
    exact sequentialCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sequentialCompletionToEventFlow_injective heq)

theorem SequentialCompletionTasteGate_single_carrier_alignment
    (x y : SequentialCompletionUp) :
    sequentialCompletionToEventFlow x = sequentialCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact SequentialCompletionTasteGate_single_carrier_alignment_direct

end BEDC.Derived.SequentialCompletionUp.TasteGate

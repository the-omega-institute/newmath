import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OptionalSamplingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OptionalSamplingUp : Type where
  | mk (P X E M T O B L H C Q N : BHist) : OptionalSamplingUp
  deriving DecidableEq

def optionalSamplingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: optionalSamplingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: optionalSamplingEncodeBHist h

def optionalSamplingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (optionalSamplingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (optionalSamplingDecodeBHist tail)

private theorem optionalSamplingDecode_encode :
    ∀ h : BHist, optionalSamplingDecodeBHist (optionalSamplingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def optionalSamplingFields : OptionalSamplingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OptionalSamplingUp.mk P X E M T O B L H C Q N => [P, X, E, M, T, O, B, L, H, C, Q, N]

def optionalSamplingToEventFlow : OptionalSamplingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (optionalSamplingFields x).map optionalSamplingEncodeBHist

private def optionalSamplingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => optionalSamplingEventAtDefault index rest

def optionalSamplingFromEventFlow (ef : EventFlow) : Option OptionalSamplingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OptionalSamplingUp.mk
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 0 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 1 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 2 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 3 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 4 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 5 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 6 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 7 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 8 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 9 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 10 ef))
      (optionalSamplingDecodeBHist (optionalSamplingEventAtDefault 11 ef)))

private theorem optionalSampling_round_trip :
    ∀ x : OptionalSamplingUp,
      optionalSamplingFromEventFlow (optionalSamplingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P X E M T O B L H C Q N =>
      change
        some
          (OptionalSamplingUp.mk
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist P))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist X))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist E))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist M))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist T))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist O))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist B))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist L))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist H))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist C))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist Q))
            (optionalSamplingDecodeBHist (optionalSamplingEncodeBHist N))) =
          some (OptionalSamplingUp.mk P X E M T O B L H C Q N)
      rw [optionalSamplingDecode_encode P, optionalSamplingDecode_encode X,
        optionalSamplingDecode_encode E, optionalSamplingDecode_encode M,
        optionalSamplingDecode_encode T, optionalSamplingDecode_encode O,
        optionalSamplingDecode_encode B, optionalSamplingDecode_encode L,
        optionalSamplingDecode_encode H, optionalSamplingDecode_encode C,
        optionalSamplingDecode_encode Q, optionalSamplingDecode_encode N]

private theorem optionalSamplingToEventFlow_injective {x y : OptionalSamplingUp} :
    optionalSamplingToEventFlow x = optionalSamplingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      optionalSamplingFromEventFlow (optionalSamplingToEventFlow x) =
        optionalSamplingFromEventFlow (optionalSamplingToEventFlow y) :=
    congrArg optionalSamplingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (optionalSampling_round_trip x).symm
      (Eq.trans hread (optionalSampling_round_trip y)))

instance optionalSamplingBHistCarrier : BHistCarrier OptionalSamplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := optionalSamplingToEventFlow
  fromEventFlow := optionalSamplingFromEventFlow

instance optionalSamplingChapterTasteGate : ChapterTasteGate OptionalSamplingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change optionalSamplingFromEventFlow (optionalSamplingToEventFlow x) = some x
    exact optionalSampling_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (optionalSamplingToEventFlow_injective heq)

theorem OptionalSamplingTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier OptionalSamplingUp) ∧ Nonempty (ChapterTasteGate OptionalSamplingUp) ∧
      (∀ h : BHist, optionalSamplingDecodeBHist (optionalSamplingEncodeBHist h) = h) ∧
        optionalSamplingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨optionalSamplingBHistCarrier⟩, ⟨optionalSamplingChapterTasteGate⟩,
      optionalSamplingDecode_encode, rfl⟩

end BEDC.Derived.OptionalSamplingUp.TasteGate

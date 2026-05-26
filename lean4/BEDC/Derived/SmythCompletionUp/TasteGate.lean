import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SmythCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SmythCompletionUp : Type where
  | mk (U Q F R D M B I H C P N : BHist) : SmythCompletionUp
  deriving DecidableEq

def smythCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: smythCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: smythCompletionEncodeBHist h

def smythCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (smythCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (smythCompletionDecodeBHist tail)

private theorem SmythCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, smythCompletionDecodeBHist (smythCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def smythCompletionFields : SmythCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SmythCompletionUp.mk U Q F R D M B I H C P N => [U, Q, F, R, D, M, B, I, H, C, P, N]

def smythCompletionToEventFlow : SmythCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (smythCompletionFields x).map smythCompletionEncodeBHist

private def smythCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => smythCompletionEventAtDefault index rest

def smythCompletionFromEventFlow (ef : EventFlow) : Option SmythCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SmythCompletionUp.mk
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 0 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 1 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 2 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 3 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 4 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 5 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 6 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 7 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 8 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 9 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 10 ef))
      (smythCompletionDecodeBHist (smythCompletionEventAtDefault 11 ef)))

private theorem SmythCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SmythCompletionUp,
      smythCompletionFromEventFlow (smythCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk U Q F R D M B I H C P N =>
      change
        some
          (SmythCompletionUp.mk
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist U))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist Q))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist F))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist R))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist D))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist M))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist B))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist I))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist H))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist C))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist P))
            (smythCompletionDecodeBHist (smythCompletionEncodeBHist N))) =
          some (SmythCompletionUp.mk U Q F R D M B I H C P N)
      rw [SmythCompletionTasteGate_single_carrier_alignment_decode U,
        SmythCompletionTasteGate_single_carrier_alignment_decode Q,
        SmythCompletionTasteGate_single_carrier_alignment_decode F,
        SmythCompletionTasteGate_single_carrier_alignment_decode R,
        SmythCompletionTasteGate_single_carrier_alignment_decode D,
        SmythCompletionTasteGate_single_carrier_alignment_decode M,
        SmythCompletionTasteGate_single_carrier_alignment_decode B,
        SmythCompletionTasteGate_single_carrier_alignment_decode I,
        SmythCompletionTasteGate_single_carrier_alignment_decode H,
        SmythCompletionTasteGate_single_carrier_alignment_decode C,
        SmythCompletionTasteGate_single_carrier_alignment_decode P,
        SmythCompletionTasteGate_single_carrier_alignment_decode N]

private theorem SmythCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SmythCompletionUp} :
    smythCompletionToEventFlow x = smythCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      smythCompletionFromEventFlow (smythCompletionToEventFlow x) =
        smythCompletionFromEventFlow (smythCompletionToEventFlow y) :=
    congrArg smythCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SmythCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SmythCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance smythCompletionBHistCarrier : BHistCarrier SmythCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := smythCompletionToEventFlow
  fromEventFlow := smythCompletionFromEventFlow

instance smythCompletionChapterTasteGate : ChapterTasteGate SmythCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change smythCompletionFromEventFlow (smythCompletionToEventFlow x) = some x
    exact SmythCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SmythCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SmythCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  smythCompletionChapterTasteGate

theorem SmythCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SmythCompletionUp) ∧
      Nonempty (ChapterTasteGate SmythCompletionUp) ∧
        (∀ h : BHist, smythCompletionDecodeBHist (smythCompletionEncodeBHist h) = h) ∧
          smythCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨smythCompletionBHistCarrier⟩,
      ⟨⟨smythCompletionChapterTasteGate⟩,
        ⟨SmythCompletionTasteGate_single_carrier_alignment_decode, rfl⟩⟩⟩

end BEDC.Derived.SmythCompletionUp

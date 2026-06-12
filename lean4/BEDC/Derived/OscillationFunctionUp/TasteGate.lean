import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OscillationFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OscillationFunctionUp : Type where
  | mk (P B D S R V H C K N : BHist) : OscillationFunctionUp
  deriving DecidableEq

def oscillationFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oscillationFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oscillationFunctionEncodeBHist h

def oscillationFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oscillationFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oscillationFunctionDecodeBHist tail)

private theorem oscillationFunctionDecodeEncode :
    ∀ h : BHist, oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oscillationFunctionFields : OscillationFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OscillationFunctionUp.mk P B D S R V H C K N => [P, B, D, S, R, V, H, C, K, N]

def oscillationFunctionToEventFlow : OscillationFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (oscillationFunctionFields x).map oscillationFunctionEncodeBHist

private def oscillationFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => oscillationFunctionEventAt index rest

def oscillationFunctionFromEventFlow (ef : EventFlow) : Option OscillationFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OscillationFunctionUp.mk
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 0 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 1 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 2 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 3 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 4 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 5 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 6 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 7 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 8 ef))
      (oscillationFunctionDecodeBHist (oscillationFunctionEventAt 9 ef)))

private theorem oscillationFunction_round_trip (x : OscillationFunctionUp) :
    oscillationFunctionFromEventFlow (oscillationFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P B D S R V H C K N =>
      change
        some
          (OscillationFunctionUp.mk
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist P))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist B))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist D))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist S))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist R))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist V))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist H))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist C))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist K))
            (oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist N))) =
          some (OscillationFunctionUp.mk P B D S R V H C K N)
      rw [oscillationFunctionDecodeEncode P, oscillationFunctionDecodeEncode B,
        oscillationFunctionDecodeEncode D, oscillationFunctionDecodeEncode S,
        oscillationFunctionDecodeEncode R, oscillationFunctionDecodeEncode V,
        oscillationFunctionDecodeEncode H, oscillationFunctionDecodeEncode C,
        oscillationFunctionDecodeEncode K, oscillationFunctionDecodeEncode N]

private theorem oscillationFunctionToEventFlow_injective {x y : OscillationFunctionUp} :
    oscillationFunctionToEventFlow x = oscillationFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oscillationFunctionFromEventFlow (oscillationFunctionToEventFlow x) =
        oscillationFunctionFromEventFlow (oscillationFunctionToEventFlow y) :=
    congrArg oscillationFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (oscillationFunction_round_trip x).symm
      (Eq.trans hread (oscillationFunction_round_trip y)))

instance oscillationFunctionBHistCarrier : BHistCarrier OscillationFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oscillationFunctionToEventFlow
  fromEventFlow := oscillationFunctionFromEventFlow

instance oscillationFunctionChapterTasteGate : ChapterTasteGate OscillationFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change oscillationFunctionFromEventFlow (oscillationFunctionToEventFlow x) = some x
    exact oscillationFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (oscillationFunctionToEventFlow_injective heq)

instance oscillationFunctionFieldFaithful : FieldFaithful OscillationFunctionUp where
  fields := oscillationFunctionFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk P₁ B₁ D₁ S₁ R₁ V₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk P₂ B₂ D₂ S₂ R₂ V₂ H₂ C₂ K₂ N₂ =>
        injection h with hP tP
        injection tP with hB tB
        injection tB with hD tD
        injection tD with hS tS
        injection tS with hR tR
        injection tR with hV tV
        injection tV with hH tH
        injection tH with hC tC
        injection tC with hK tK
        injection tK with hN _
        subst hP
        subst hB
        subst hD
        subst hS
        subst hR
        subst hV
        subst hH
        subst hC
        subst hK
        subst hN
        rfl

theorem OscillationFunctionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier OscillationFunctionUp) ∧
      Nonempty (ChapterTasteGate OscillationFunctionUp) ∧
        Nonempty (FieldFaithful OscillationFunctionUp) ∧
          oscillationFunctionEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            oscillationFunctionEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] ∧
              (∀ h : BHist,
                oscillationFunctionDecodeBHist (oscillationFunctionEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨oscillationFunctionBHistCarrier⟩, ⟨oscillationFunctionChapterTasteGate⟩,
      ⟨oscillationFunctionFieldFaithful⟩, rfl, rfl, oscillationFunctionDecodeEncode⟩

end BEDC.Derived.OscillationFunctionUp

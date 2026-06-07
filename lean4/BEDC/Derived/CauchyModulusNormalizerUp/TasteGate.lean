import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusNormalizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusNormalizerUp : Type where
  | mk (S M T D W R Q E H C P N : BHist) : CauchyModulusNormalizerUp
  deriving DecidableEq

def cauchyModulusNormalizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusNormalizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusNormalizerEncodeBHist h

def cauchyModulusNormalizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusNormalizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusNormalizerDecodeBHist tail)

private theorem cauchyModulusNormalizerDecodeEncode :
    ∀ h : BHist,
      cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusNormalizerFields : CauchyModulusNormalizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusNormalizerUp.mk S M T D W R Q E H C P N =>
      [S, M, T, D, W, R, Q, E, H, C, P, N]

def cauchyModulusNormalizerToEventFlow : CauchyModulusNormalizerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyModulusNormalizerFields x).map cauchyModulusNormalizerEncodeBHist

private def cauchyModulusNormalizerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusNormalizerEventAtDefault index rest

def cauchyModulusNormalizerFromEventFlow
    (ef : EventFlow) : Option CauchyModulusNormalizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusNormalizerUp.mk
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 0 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 1 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 2 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 3 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 4 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 5 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 6 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 7 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 8 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 9 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 10 ef))
      (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEventAtDefault 11 ef)))

private theorem cauchyModulusNormalizerRoundTrip :
    ∀ x : CauchyModulusNormalizerUp,
      cauchyModulusNormalizerFromEventFlow (cauchyModulusNormalizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M T D W R Q E H C P N =>
      change
        some
          (CauchyModulusNormalizerUp.mk
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist S))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist M))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist T))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist D))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist W))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist R))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist Q))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist E))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist H))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist C))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist P))
            (cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist N))) =
          some (CauchyModulusNormalizerUp.mk S M T D W R Q E H C P N)
      rw [cauchyModulusNormalizerDecodeEncode S, cauchyModulusNormalizerDecodeEncode M,
        cauchyModulusNormalizerDecodeEncode T, cauchyModulusNormalizerDecodeEncode D,
        cauchyModulusNormalizerDecodeEncode W, cauchyModulusNormalizerDecodeEncode R,
        cauchyModulusNormalizerDecodeEncode Q, cauchyModulusNormalizerDecodeEncode E,
        cauchyModulusNormalizerDecodeEncode H, cauchyModulusNormalizerDecodeEncode C,
        cauchyModulusNormalizerDecodeEncode P, cauchyModulusNormalizerDecodeEncode N]

private theorem cauchyModulusNormalizerToEventFlow_injective
    {x y : CauchyModulusNormalizerUp} :
    cauchyModulusNormalizerToEventFlow x = cauchyModulusNormalizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusNormalizerFromEventFlow (cauchyModulusNormalizerToEventFlow x) =
        cauchyModulusNormalizerFromEventFlow (cauchyModulusNormalizerToEventFlow y) :=
    congrArg cauchyModulusNormalizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusNormalizerRoundTrip x).symm
      (Eq.trans hread (cauchyModulusNormalizerRoundTrip y)))

private theorem cauchyModulusNormalizerFieldFaithful :
    ∀ x y : CauchyModulusNormalizerUp,
      cauchyModulusNormalizerFields x = cauchyModulusNormalizerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ T₁ D₁ W₁ R₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ T₂ D₂ W₂ R₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyModulusNormalizerBHistCarrier : BHistCarrier CauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusNormalizerToEventFlow
  fromEventFlow := cauchyModulusNormalizerFromEventFlow

instance cauchyModulusNormalizerChapterTasteGate :
    ChapterTasteGate CauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusNormalizerFromEventFlow (cauchyModulusNormalizerToEventFlow x) = some x
    exact cauchyModulusNormalizerRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusNormalizerToEventFlow_injective heq)

instance cauchyModulusNormalizerFieldFaithfulInst :
    FieldFaithful CauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusNormalizerFields
  field_faithful := cauchyModulusNormalizerFieldFaithful

instance cauchyModulusNormalizerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyModulusNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyModulusNormalizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyModulusNormalizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyModulusNormalizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusNormalizerChapterTasteGate

theorem CauchyModulusNormalizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusNormalizerDecodeBHist (cauchyModulusNormalizerEncodeBHist h) = h) ∧
      (∀ x : CauchyModulusNormalizerUp,
        cauchyModulusNormalizerFromEventFlow (cauchyModulusNormalizerToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyModulusNormalizerUp,
          cauchyModulusNormalizerToEventFlow x = cauchyModulusNormalizerToEventFlow y →
            x = y) ∧
          cauchyModulusNormalizerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact cauchyModulusNormalizerDecodeEncode
  constructor
  · exact cauchyModulusNormalizerRoundTrip
  constructor
  · intro x y heq
    exact cauchyModulusNormalizerToEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyModulusNormalizerUp

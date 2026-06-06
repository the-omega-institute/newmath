import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HilbertAlexanderBlockerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HilbertAlexanderBlockerUp : Type where
  | mk : (S P T B F L A R C Q N : BHist) → HilbertAlexanderBlockerUp
  deriving DecidableEq

def hilbertAlexanderBlockerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hilbertAlexanderBlockerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hilbertAlexanderBlockerEncodeBHist h

def hilbertAlexanderBlockerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hilbertAlexanderBlockerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hilbertAlexanderBlockerDecodeBHist tail)

private theorem hilbertAlexanderBlockerDecode_encode_bhist :
    ∀ h : BHist, hilbertAlexanderBlockerDecodeBHist
      (hilbertAlexanderBlockerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hilbertAlexanderBlockerFields :
    HilbertAlexanderBlockerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HilbertAlexanderBlockerUp.mk S P T B F L A R C Q N => [S, P, T, B, F, L, A, R, C, Q, N]

def hilbertAlexanderBlockerToEventFlow :
    HilbertAlexanderBlockerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hilbertAlexanderBlockerFields x).map hilbertAlexanderBlockerEncodeBHist

def hilbertAlexanderBlockerFromEventFlow :
    EventFlow → Option HilbertAlexanderBlockerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, P, T, B, F, L, A, R, C, Q, N] =>
      some
        (HilbertAlexanderBlockerUp.mk
          (hilbertAlexanderBlockerDecodeBHist S)
          (hilbertAlexanderBlockerDecodeBHist P)
          (hilbertAlexanderBlockerDecodeBHist T)
          (hilbertAlexanderBlockerDecodeBHist B)
          (hilbertAlexanderBlockerDecodeBHist F)
          (hilbertAlexanderBlockerDecodeBHist L)
          (hilbertAlexanderBlockerDecodeBHist A)
          (hilbertAlexanderBlockerDecodeBHist R)
          (hilbertAlexanderBlockerDecodeBHist C)
          (hilbertAlexanderBlockerDecodeBHist Q)
          (hilbertAlexanderBlockerDecodeBHist N))
  | _ => none

private theorem hilbertAlexanderBlocker_round_trip :
    ∀ x : HilbertAlexanderBlockerUp,
      hilbertAlexanderBlockerFromEventFlow (hilbertAlexanderBlockerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S P T B F L A R C Q N =>
      change
        some
          (HilbertAlexanderBlockerUp.mk
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist S))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist P))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist T))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist B))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist F))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist L))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist A))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist R))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist C))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist Q))
            (hilbertAlexanderBlockerDecodeBHist (hilbertAlexanderBlockerEncodeBHist N))) =
          some (HilbertAlexanderBlockerUp.mk S P T B F L A R C Q N)
      rw [hilbertAlexanderBlockerDecode_encode_bhist S,
        hilbertAlexanderBlockerDecode_encode_bhist P,
        hilbertAlexanderBlockerDecode_encode_bhist T,
        hilbertAlexanderBlockerDecode_encode_bhist B,
        hilbertAlexanderBlockerDecode_encode_bhist F,
        hilbertAlexanderBlockerDecode_encode_bhist L,
        hilbertAlexanderBlockerDecode_encode_bhist A,
        hilbertAlexanderBlockerDecode_encode_bhist R,
        hilbertAlexanderBlockerDecode_encode_bhist C,
        hilbertAlexanderBlockerDecode_encode_bhist Q,
        hilbertAlexanderBlockerDecode_encode_bhist N]

private theorem hilbertAlexanderBlockerToEventFlow_injective
    {x y : HilbertAlexanderBlockerUp} :
    hilbertAlexanderBlockerToEventFlow x = hilbertAlexanderBlockerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hilbertAlexanderBlockerFromEventFlow (hilbertAlexanderBlockerToEventFlow x) =
        hilbertAlexanderBlockerFromEventFlow (hilbertAlexanderBlockerToEventFlow y) :=
    congrArg hilbertAlexanderBlockerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hilbertAlexanderBlocker_round_trip x).symm
      (Eq.trans hread (hilbertAlexanderBlocker_round_trip y)))

private theorem hilbertAlexanderBlocker_field_faithful :
    ∀ x y : HilbertAlexanderBlockerUp,
      hilbertAlexanderBlockerFields x = hilbertAlexanderBlockerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S P T B F L A R C Q N =>
      cases y with
      | mk S' P' T' B' F' L' A' R' C' Q' N' =>
          cases hfields
          rfl

instance hilbertAlexanderBlockerBHistCarrier :
    BHistCarrier HilbertAlexanderBlockerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hilbertAlexanderBlockerToEventFlow
  fromEventFlow := hilbertAlexanderBlockerFromEventFlow

instance hilbertAlexanderBlockerChapterTasteGate :
    ChapterTasteGate HilbertAlexanderBlockerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hilbertAlexanderBlockerFromEventFlow (hilbertAlexanderBlockerToEventFlow x) =
      some x
    exact hilbertAlexanderBlocker_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hilbertAlexanderBlockerToEventFlow_injective heq)

instance hilbertAlexanderBlockerFieldFaithful :
    FieldFaithful HilbertAlexanderBlockerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hilbertAlexanderBlockerFields
  field_faithful := hilbertAlexanderBlocker_field_faithful

instance hilbertAlexanderBlockerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HilbertAlexanderBlockerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HilbertAlexanderBlockerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HilbertAlexanderBlockerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HilbertAlexanderBlockerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hilbertAlexanderBlockerChapterTasteGate

end BEDC.Derived.HilbertAlexanderBlockerUp

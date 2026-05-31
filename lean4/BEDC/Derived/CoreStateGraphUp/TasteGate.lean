import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CoreStateGraphUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CoreStateGraphUp : Type where
  | mk (V E K M T H C P N : BHist) : CoreStateGraphUp
  deriving DecidableEq

def coreStateGraphEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: coreStateGraphEncodeBHist h
  | BHist.e1 h => BMark.b1 :: coreStateGraphEncodeBHist h

def coreStateGraphDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (coreStateGraphDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (coreStateGraphDecodeBHist tail)

private theorem coreStateGraphDecode_encode_bhist :
    ∀ h : BHist, coreStateGraphDecodeBHist (coreStateGraphEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def coreStateGraphFields : CoreStateGraphUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CoreStateGraphUp.mk V E K M T H C P N => [V, E, K, M, T, H, C, P, N]

def coreStateGraphToEventFlow : CoreStateGraphUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (coreStateGraphFields x).map coreStateGraphEncodeBHist

private def coreStateGraphRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => coreStateGraphRawAt n rest

def coreStateGraphFromEventFlow (flow : EventFlow) : Option CoreStateGraphUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CoreStateGraphUp.mk
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 0 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 1 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 2 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 3 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 4 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 5 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 6 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 7 flow))
      (coreStateGraphDecodeBHist (coreStateGraphRawAt 8 flow)))

private theorem coreStateGraph_round_trip :
    ∀ x : CoreStateGraphUp,
      coreStateGraphFromEventFlow (coreStateGraphToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V E K M T H C P N =>
      change
        some
          (CoreStateGraphUp.mk
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist V))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist E))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist K))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist M))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist T))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist H))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist C))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist P))
            (coreStateGraphDecodeBHist (coreStateGraphEncodeBHist N))) =
          some (CoreStateGraphUp.mk V E K M T H C P N)
      rw [coreStateGraphDecode_encode_bhist V, coreStateGraphDecode_encode_bhist E,
        coreStateGraphDecode_encode_bhist K, coreStateGraphDecode_encode_bhist M,
        coreStateGraphDecode_encode_bhist T, coreStateGraphDecode_encode_bhist H,
        coreStateGraphDecode_encode_bhist C, coreStateGraphDecode_encode_bhist P,
        coreStateGraphDecode_encode_bhist N]

private theorem coreStateGraphToEventFlow_injective {x y : CoreStateGraphUp} :
    coreStateGraphToEventFlow x = coreStateGraphToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      coreStateGraphFromEventFlow (coreStateGraphToEventFlow x) =
        coreStateGraphFromEventFlow (coreStateGraphToEventFlow y) :=
    congrArg coreStateGraphFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (coreStateGraph_round_trip x).symm
      (Eq.trans hread (coreStateGraph_round_trip y)))

private theorem coreStateGraph_fields_faithful :
    ∀ x y : CoreStateGraphUp, coreStateGraphFields x = coreStateGraphFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V₁ E₁ K₁ M₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk V₂ E₂ K₂ M₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance coreStateGraphBHistCarrier : BHistCarrier CoreStateGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := coreStateGraphToEventFlow
  fromEventFlow := coreStateGraphFromEventFlow

instance coreStateGraphChapterTasteGate : ChapterTasteGate CoreStateGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change coreStateGraphFromEventFlow (coreStateGraphToEventFlow x) = some x
    exact coreStateGraph_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (coreStateGraphToEventFlow_injective heq)

instance coreStateGraphFieldFaithful : FieldFaithful CoreStateGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := coreStateGraphFields
  field_faithful := coreStateGraph_fields_faithful

instance coreStateGraphNontrivial : Nontrivial CoreStateGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CoreStateGraphUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CoreStateGraphUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CoreStateGraphUp :=
  -- BEDC touchpoint anchor: BHist BMark
  coreStateGraphChapterTasteGate

theorem CoreStateGraphTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CoreStateGraphUp) ∧
      Nonempty (FieldFaithful CoreStateGraphUp) ∧
        Nonempty (Nontrivial CoreStateGraphUp) ∧
          (∀ h : BHist, coreStateGraphDecodeBHist (coreStateGraphEncodeBHist h) = h) ∧
            (∀ x : CoreStateGraphUp,
              coreStateGraphFromEventFlow (coreStateGraphToEventFlow x) = some x) ∧
              (∀ x y : CoreStateGraphUp,
                coreStateGraphToEventFlow x = coreStateGraphToEventFlow y → x = y) ∧
                coreStateGraphEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨coreStateGraphChapterTasteGate⟩,
      ⟨coreStateGraphFieldFaithful⟩,
      ⟨coreStateGraphNontrivial⟩,
      coreStateGraphDecode_encode_bhist,
      coreStateGraph_round_trip,
      (fun _ _ heq => coreStateGraphToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CoreStateGraphUp

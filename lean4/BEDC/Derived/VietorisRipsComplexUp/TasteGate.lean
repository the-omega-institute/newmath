import BEDC.Derived.VietorisRipsComplexUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VietorisRipsComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def vietorisRipsComplexEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: vietorisRipsComplexEncodeBHist h
  | BHist.e1 h => BMark.b1 :: vietorisRipsComplexEncodeBHist h

def vietorisRipsComplexDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (vietorisRipsComplexDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (vietorisRipsComplexDecodeBHist tail)

private theorem VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def vietorisRipsComplexFields : _root_.BEDC.Derived.VietorisRipsComplexUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.VietorisRipsComplexUp.packet metric vertexLedger threshold
      pairwiseDistance simplicialHandoff transport replay provenance localName =>
        [metric, vertexLedger, threshold, pairwiseDistance, simplicialHandoff, transport,
          replay, provenance, localName]

def vietorisRipsComplexToEventFlow :
    _root_.BEDC.Derived.VietorisRipsComplexUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (vietorisRipsComplexFields x).map vietorisRipsComplexEncodeBHist

private def vietorisRipsComplexRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => vietorisRipsComplexRawAt index rest

def vietorisRipsComplexFromEventFlow
    (flow : EventFlow) : Option _root_.BEDC.Derived.VietorisRipsComplexUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (_root_.BEDC.Derived.VietorisRipsComplexUp.packet
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 0 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 1 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 2 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 3 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 4 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 5 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 6 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 7 flow))
      (vietorisRipsComplexDecodeBHist (vietorisRipsComplexRawAt 8 flow)))

private theorem VietorisRipsComplexUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : _root_.BEDC.Derived.VietorisRipsComplexUp,
      vietorisRipsComplexFromEventFlow (vietorisRipsComplexToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | packet metric vertexLedger threshold pairwiseDistance simplicialHandoff transport replay
      provenance localName =>
      change
        some
          (_root_.BEDC.Derived.VietorisRipsComplexUp.packet
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist metric))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist vertexLedger))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist threshold))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist pairwiseDistance))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist simplicialHandoff))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist transport))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist replay))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist provenance))
            (vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist localName))) =
          some
            (_root_.BEDC.Derived.VietorisRipsComplexUp.packet metric vertexLedger threshold
              pairwiseDistance simplicialHandoff transport replay provenance localName)
      rw [VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode metric,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode vertexLedger,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode threshold,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode pairwiseDistance,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode simplicialHandoff,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode transport,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode replay,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode provenance,
        VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode localName]

private theorem vietorisRipsComplexToEventFlow_injective
    {x y : _root_.BEDC.Derived.VietorisRipsComplexUp} :
    vietorisRipsComplexToEventFlow x = vietorisRipsComplexToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      vietorisRipsComplexFromEventFlow (vietorisRipsComplexToEventFlow x) =
        vietorisRipsComplexFromEventFlow (vietorisRipsComplexToEventFlow y) :=
    congrArg vietorisRipsComplexFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (VietorisRipsComplexUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (VietorisRipsComplexUpTasteGate_single_carrier_alignment_round_trip y)))

instance vietorisRipsComplexBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.VietorisRipsComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := vietorisRipsComplexToEventFlow
  fromEventFlow := vietorisRipsComplexFromEventFlow

instance vietorisRipsComplexChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.VietorisRipsComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change vietorisRipsComplexFromEventFlow (vietorisRipsComplexToEventFlow x) = some x
    exact VietorisRipsComplexUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (vietorisRipsComplexToEventFlow_injective heq)

def taste_gate : ChapterTasteGate _root_.BEDC.Derived.VietorisRipsComplexUp :=
  -- BEDC touchpoint anchor: BHist BMark
  vietorisRipsComplexChapterTasteGate

theorem VietorisRipsComplexUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, vietorisRipsComplexDecodeBHist (vietorisRipsComplexEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier _root_.BEDC.Derived.VietorisRipsComplexUp) ∧
        Nonempty (ChapterTasteGate _root_.BEDC.Derived.VietorisRipsComplexUp) ∧
          vietorisRipsComplexEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨VietorisRipsComplexUpTasteGate_single_carrier_alignment_decode,
      ⟨vietorisRipsComplexBHistCarrier⟩,
      ⟨vietorisRipsComplexChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.VietorisRipsComplexUp

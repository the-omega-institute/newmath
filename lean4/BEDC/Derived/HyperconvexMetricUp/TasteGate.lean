import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperconvexMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperconvexMetricUp : Type where
  | mk (M K B F R I E H C P N : BHist) : HyperconvexMetricUp

def hyperconvexMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperconvexMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperconvexMetricEncodeBHist h

def hyperconvexMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperconvexMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperconvexMetricDecodeBHist tail)

private theorem hyperconvexMetric_decode_encode_bhist :
    ∀ h : BHist, hyperconvexMetricDecodeBHist (hyperconvexMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem hyperconvexMetricEncodeBHist_injective {h k : BHist} :
    hyperconvexMetricEncodeBHist h = hyperconvexMetricEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      hyperconvexMetricDecodeBHist (hyperconvexMetricEncodeBHist h) =
        hyperconvexMetricDecodeBHist (hyperconvexMetricEncodeBHist k) :=
    congrArg hyperconvexMetricDecodeBHist heq
  exact
    Eq.trans (hyperconvexMetric_decode_encode_bhist h).symm
      (Eq.trans hdecode (hyperconvexMetric_decode_encode_bhist k))

private theorem hyperconvexMetric_mk_congr
    {M M' K K' B B' F F' R R' I I' E E' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hK : K' = K) (hB : B' = B) (hF : F' = F) (hR : R' = R)
    (hI : I' = I) (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    HyperconvexMetricUp.mk M' K' B' F' R' I' E' H' C' P' N' =
      HyperconvexMetricUp.mk M K B F R I E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hK
  cases hB
  cases hF
  cases hR
  cases hI
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def hyperconvexMetricToEventFlow : HyperconvexMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HyperconvexMetricUp.mk M K B F R I E H C P N =>
      [hyperconvexMetricEncodeBHist M, hyperconvexMetricEncodeBHist K,
        hyperconvexMetricEncodeBHist B, hyperconvexMetricEncodeBHist F,
        hyperconvexMetricEncodeBHist R, hyperconvexMetricEncodeBHist I,
        hyperconvexMetricEncodeBHist E, hyperconvexMetricEncodeBHist H,
        hyperconvexMetricEncodeBHist C, hyperconvexMetricEncodeBHist P,
        hyperconvexMetricEncodeBHist N]

private def hyperconvexMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperconvexMetricEventAtDefault index rest

def hyperconvexMetricFromEventFlow (ef : EventFlow) : Option HyperconvexMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperconvexMetricUp.mk
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 0 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 1 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 2 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 3 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 4 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 5 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 6 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 7 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 8 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 9 ef))
      (hyperconvexMetricDecodeBHist (hyperconvexMetricEventAtDefault 10 ef)))

private theorem hyperconvexMetric_round_trip :
    ∀ x : HyperconvexMetricUp,
      hyperconvexMetricFromEventFlow (hyperconvexMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K B F R I E H C P N =>
      exact
        congrArg some
          (hyperconvexMetric_mk_congr
            (hyperconvexMetric_decode_encode_bhist M)
            (hyperconvexMetric_decode_encode_bhist K)
            (hyperconvexMetric_decode_encode_bhist B)
            (hyperconvexMetric_decode_encode_bhist F)
            (hyperconvexMetric_decode_encode_bhist R)
            (hyperconvexMetric_decode_encode_bhist I)
            (hyperconvexMetric_decode_encode_bhist E)
            (hyperconvexMetric_decode_encode_bhist H)
            (hyperconvexMetric_decode_encode_bhist C)
            (hyperconvexMetric_decode_encode_bhist P)
            (hyperconvexMetric_decode_encode_bhist N))

private theorem hyperconvexMetricToEventFlow_injective {x y : HyperconvexMetricUp} :
    hyperconvexMetricToEventFlow x = hyperconvexMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk M K B F R I E H C P N =>
      cases y with
      | mk M' K' B' F' R' I' E' H' C' P' N' =>
          injection heq with MEq tailEq1
          injection tailEq1 with KEq tailEq2
          injection tailEq2 with BEq tailEq3
          injection tailEq3 with FEq tailEq4
          injection tailEq4 with REq tailEq5
          injection tailEq5 with IEq tailEq6
          injection tailEq6 with EEq tailEq7
          injection tailEq7 with HEq tailEq8
          injection tailEq8 with CEq tailEq9
          injection tailEq9 with PEq tailEq10
          injection tailEq10 with NEq _nilEq
          exact
            hyperconvexMetric_mk_congr
              (hyperconvexMetricEncodeBHist_injective MEq)
              (hyperconvexMetricEncodeBHist_injective KEq)
              (hyperconvexMetricEncodeBHist_injective BEq)
              (hyperconvexMetricEncodeBHist_injective FEq)
              (hyperconvexMetricEncodeBHist_injective REq)
              (hyperconvexMetricEncodeBHist_injective IEq)
              (hyperconvexMetricEncodeBHist_injective EEq)
              (hyperconvexMetricEncodeBHist_injective HEq)
              (hyperconvexMetricEncodeBHist_injective CEq)
              (hyperconvexMetricEncodeBHist_injective PEq)
              (hyperconvexMetricEncodeBHist_injective NEq)

instance hyperconvexMetricBHistCarrier : BHistCarrier HyperconvexMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperconvexMetricToEventFlow
  fromEventFlow := hyperconvexMetricFromEventFlow

instance hyperconvexMetricChapterTasteGate : ChapterTasteGate HyperconvexMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperconvexMetricFromEventFlow (hyperconvexMetricToEventFlow x) = some x
    exact hyperconvexMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperconvexMetricToEventFlow_injective heq)

theorem HyperconvexMetricTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier HyperconvexMetricUp,
      Nonempty (@ChapterTasteGate HyperconvexMetricUp carrier)) ∧
        (∀ h : BHist, hyperconvexMetricDecodeBHist (hyperconvexMetricEncodeBHist h) = h) ∧
          (∀ x : HyperconvexMetricUp,
            hyperconvexMetricFromEventFlow (hyperconvexMetricToEventFlow x) = some x) ∧
            hyperconvexMetricEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  let carrier : BHistCarrier HyperconvexMetricUp :=
    { toEventFlow := hyperconvexMetricToEventFlow
      fromEventFlow := hyperconvexMetricFromEventFlow }
  let gate : @ChapterTasteGate HyperconvexMetricUp carrier :=
    { round_trip := by
        intro x
        exact hyperconvexMetric_round_trip x
      layer_separation := by
        intro x y hxy heq
        exact hxy (hyperconvexMetricToEventFlow_injective heq) }
  exact
    ⟨⟨carrier, ⟨gate⟩⟩, hyperconvexMetric_decode_encode_bhist,
      hyperconvexMetric_round_trip, rfl⟩

end BEDC.Derived.HyperconvexMetricUp

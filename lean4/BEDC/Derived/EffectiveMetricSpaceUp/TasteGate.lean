import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveMetricSpaceUp : Type where
  | mk (X S W rho D R delta Sigma Delta T C P N : BHist) : EffectiveMetricSpaceUp

def effectiveMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveMetricSpaceEncodeBHist h

def effectiveMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveMetricSpaceDecodeBHist tail)

private theorem effectiveMetricSpace_decode_encode_bhist :
    ∀ h : BHist, effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem effectiveMetricSpaceEncodeBHist_injective {h k : BHist} :
    effectiveMetricSpaceEncodeBHist h = effectiveMetricSpaceEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEncodeBHist h) =
        effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEncodeBHist k) :=
    congrArg effectiveMetricSpaceDecodeBHist heq
  exact
    Eq.trans (effectiveMetricSpace_decode_encode_bhist h).symm
      (Eq.trans hdecode (effectiveMetricSpace_decode_encode_bhist k))

private theorem effectiveMetricSpace_mk_congr
    {X X' S S' W W' rho rho' D D' R R' delta delta' Sigma Sigma' Delta Delta'
      T T' C C' P P' N N' : BHist}
    (hX : X' = X) (hS : S' = S) (hW : W' = W) (hRho : rho' = rho)
    (hD : D' = D) (hR : R' = R) (hDeltaSeal : delta' = delta)
    (hSigma : Sigma' = Sigma) (hDelta : Delta' = Delta) (hT : T' = T)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    EffectiveMetricSpaceUp.mk X' S' W' rho' D' R' delta' Sigma' Delta' T' C' P' N' =
      EffectiveMetricSpaceUp.mk X S W rho D R delta Sigma Delta T C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hS
  cases hW
  cases hRho
  cases hD
  cases hR
  cases hDeltaSeal
  cases hSigma
  cases hDelta
  cases hT
  cases hC
  cases hP
  cases hN
  rfl

def effectiveMetricSpaceToEventFlow : EffectiveMetricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveMetricSpaceUp.mk X S W rho D R delta Sigma Delta T C P N =>
      [effectiveMetricSpaceEncodeBHist X, effectiveMetricSpaceEncodeBHist S,
        effectiveMetricSpaceEncodeBHist W, effectiveMetricSpaceEncodeBHist rho,
        effectiveMetricSpaceEncodeBHist D, effectiveMetricSpaceEncodeBHist R,
        effectiveMetricSpaceEncodeBHist delta, effectiveMetricSpaceEncodeBHist Sigma,
        effectiveMetricSpaceEncodeBHist Delta, effectiveMetricSpaceEncodeBHist T,
        effectiveMetricSpaceEncodeBHist C, effectiveMetricSpaceEncodeBHist P,
        effectiveMetricSpaceEncodeBHist N]

private def effectiveMetricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveMetricSpaceEventAtDefault index rest

def effectiveMetricSpaceFromEventFlow (ef : EventFlow) : Option EffectiveMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectiveMetricSpaceUp.mk
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 0 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 1 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 2 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 3 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 4 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 5 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 6 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 7 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 8 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 9 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 10 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 11 ef))
      (effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEventAtDefault 12 ef)))

private theorem effectiveMetricSpace_round_trip :
    ∀ x : EffectiveMetricSpaceUp,
      effectiveMetricSpaceFromEventFlow (effectiveMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X S W rho D R delta Sigma Delta T C P N =>
      exact
        congrArg some
          (effectiveMetricSpace_mk_congr
            (effectiveMetricSpace_decode_encode_bhist X)
            (effectiveMetricSpace_decode_encode_bhist S)
            (effectiveMetricSpace_decode_encode_bhist W)
            (effectiveMetricSpace_decode_encode_bhist rho)
            (effectiveMetricSpace_decode_encode_bhist D)
            (effectiveMetricSpace_decode_encode_bhist R)
            (effectiveMetricSpace_decode_encode_bhist delta)
            (effectiveMetricSpace_decode_encode_bhist Sigma)
            (effectiveMetricSpace_decode_encode_bhist Delta)
            (effectiveMetricSpace_decode_encode_bhist T)
            (effectiveMetricSpace_decode_encode_bhist C)
            (effectiveMetricSpace_decode_encode_bhist P)
            (effectiveMetricSpace_decode_encode_bhist N))

private theorem effectiveMetricSpaceToEventFlow_injective {x y : EffectiveMetricSpaceUp} :
    effectiveMetricSpaceToEventFlow x = effectiveMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk X S W rho D R delta Sigma Delta T C P N =>
      cases y with
      | mk X' S' W' rho' D' R' delta' Sigma' Delta' T' C' P' N' =>
          injection heq with XEq tailEq1
          injection tailEq1 with SEq tailEq2
          injection tailEq2 with WEq tailEq3
          injection tailEq3 with rhoEq tailEq4
          injection tailEq4 with DEq tailEq5
          injection tailEq5 with REq tailEq6
          injection tailEq6 with deltaEq tailEq7
          injection tailEq7 with SigmaEq tailEq8
          injection tailEq8 with DeltaEq tailEq9
          injection tailEq9 with TEq tailEq10
          injection tailEq10 with CEq tailEq11
          injection tailEq11 with PEq tailEq12
          injection tailEq12 with NEq _nilEq
          exact
            effectiveMetricSpace_mk_congr
              (effectiveMetricSpaceEncodeBHist_injective XEq)
              (effectiveMetricSpaceEncodeBHist_injective SEq)
              (effectiveMetricSpaceEncodeBHist_injective WEq)
              (effectiveMetricSpaceEncodeBHist_injective rhoEq)
              (effectiveMetricSpaceEncodeBHist_injective DEq)
              (effectiveMetricSpaceEncodeBHist_injective REq)
              (effectiveMetricSpaceEncodeBHist_injective deltaEq)
              (effectiveMetricSpaceEncodeBHist_injective SigmaEq)
              (effectiveMetricSpaceEncodeBHist_injective DeltaEq)
              (effectiveMetricSpaceEncodeBHist_injective TEq)
              (effectiveMetricSpaceEncodeBHist_injective CEq)
              (effectiveMetricSpaceEncodeBHist_injective PEq)
              (effectiveMetricSpaceEncodeBHist_injective NEq)

instance effectiveMetricSpaceBHistCarrier : BHistCarrier EffectiveMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveMetricSpaceToEventFlow
  fromEventFlow := effectiveMetricSpaceFromEventFlow

instance effectiveMetricSpaceChapterTasteGate : ChapterTasteGate EffectiveMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveMetricSpaceFromEventFlow (effectiveMetricSpaceToEventFlow x) = some x
    exact effectiveMetricSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveMetricSpaceToEventFlow_injective heq)

theorem EffectiveMetricSpaceTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier EffectiveMetricSpaceUp,
      Nonempty (@ChapterTasteGate EffectiveMetricSpaceUp carrier)) ∧
        (∀ h : BHist, effectiveMetricSpaceDecodeBHist (effectiveMetricSpaceEncodeBHist h) = h) ∧
          (∀ x : EffectiveMetricSpaceUp,
            effectiveMetricSpaceFromEventFlow (effectiveMetricSpaceToEventFlow x) = some x) ∧
            effectiveMetricSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  let carrier : BHistCarrier EffectiveMetricSpaceUp :=
    { toEventFlow := effectiveMetricSpaceToEventFlow
      fromEventFlow := effectiveMetricSpaceFromEventFlow }
  let gate : @ChapterTasteGate EffectiveMetricSpaceUp carrier :=
    { round_trip := by
        intro x
        exact effectiveMetricSpace_round_trip x
      layer_separation := by
        intro x y hxy heq
        exact hxy (effectiveMetricSpaceToEventFlow_injective heq) }
  exact
    ⟨⟨carrier, ⟨gate⟩⟩, effectiveMetricSpace_decode_encode_bhist,
      effectiveMetricSpace_round_trip, rfl⟩

end BEDC.Derived.EffectiveMetricSpaceUp

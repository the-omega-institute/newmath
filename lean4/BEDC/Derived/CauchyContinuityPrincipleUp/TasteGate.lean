import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuityPrincipleUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContinuityPrincipleUp : Type where
  | mk (S W D M U T E H C P N : BHist) : CauchyContinuityPrincipleUp
  deriving DecidableEq

def cauchyContinuityPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuityPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuityPrincipleEncodeBHist h

def cauchyContinuityPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuityPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuityPrincipleDecodeBHist tail)

private theorem CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContinuityPrincipleFields : CauchyContinuityPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuityPrincipleUp.mk S W D M U T E H C P N =>
      [S, W, D, M, U, T, E, H, C, P, N]

def cauchyContinuityPrincipleToEventFlow : CauchyContinuityPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyContinuityPrincipleFields x).map cauchyContinuityPrincipleEncodeBHist

private def cauchyContinuityPrincipleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyContinuityPrincipleEventAt index rest

def cauchyContinuityPrincipleFromEventFlow (ef : EventFlow) :
    Option CauchyContinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyContinuityPrincipleUp.mk
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 0 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 1 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 2 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 3 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 4 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 5 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 6 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 7 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 8 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 9 ef))
      (cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEventAt 10 ef)))

private theorem cauchyContinuityPrinciple_mk_congr
    {S S' W W' D D' M M' U U' T T' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hW : W' = W) (hD : D' = D) (hM : M' = M)
    (hU : U' = U) (hT : T' = T) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyContinuityPrincipleUp.mk S' W' D' M' U' T' E' H' C' P' N' =
      CauchyContinuityPrincipleUp.mk S W D M U T E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hW
  cases hD
  cases hM
  cases hU
  cases hT
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyContinuityPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyContinuityPrincipleUp,
      cauchyContinuityPrincipleFromEventFlow (cauchyContinuityPrincipleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D M U T E H C P N =>
      exact
        congrArg some
          (cauchyContinuityPrinciple_mk_congr
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode S)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode W)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode D)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode M)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode U)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode T)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode E)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode H)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode C)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode P)
            (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode N))

private theorem cauchyContinuityPrincipleToEventFlow_injective
    {x y : CauchyContinuityPrincipleUp} :
    cauchyContinuityPrincipleToEventFlow x = cauchyContinuityPrincipleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuityPrincipleFromEventFlow (cauchyContinuityPrincipleToEventFlow x) =
        cauchyContinuityPrincipleFromEventFlow (cauchyContinuityPrincipleToEventFlow y) :=
    congrArg cauchyContinuityPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyContinuityPrincipleTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyContinuityPrinciple_field_faithful :
    ∀ x y : CauchyContinuityPrincipleUp,
      cauchyContinuityPrincipleFields x = cauchyContinuityPrincipleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S W D M U T E H C P N =>
      cases y with
      | mk S' W' D' M' U' T' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyContinuityPrincipleBHistCarrier :
    BHistCarrier CauchyContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuityPrincipleToEventFlow
  fromEventFlow := cauchyContinuityPrincipleFromEventFlow

instance cauchyContinuityPrincipleChapterTasteGate :
    ChapterTasteGate CauchyContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyContinuityPrincipleFromEventFlow (cauchyContinuityPrincipleToEventFlow x) =
      some x
    exact CauchyContinuityPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyContinuityPrincipleToEventFlow_injective heq)

instance cauchyContinuityPrincipleFieldFaithful :
    FieldFaithful CauchyContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyContinuityPrincipleFields
  field_faithful := cauchyContinuityPrinciple_field_faithful

instance cauchyContinuityPrincipleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyContinuityPrincipleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyContinuityPrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyContinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyContinuityPrincipleChapterTasteGate

theorem CauchyContinuityPrincipleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyContinuityPrincipleUp) ∧
      Nonempty (FieldFaithful CauchyContinuityPrincipleUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyContinuityPrincipleUp) ∧
      (∀ h : BHist,
        cauchyContinuityPrincipleDecodeBHist (cauchyContinuityPrincipleEncodeBHist h) =
          h) ∧
      (∀ x : CauchyContinuityPrincipleUp,
        cauchyContinuityPrincipleFromEventFlow (cauchyContinuityPrincipleToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyContinuityPrincipleUp,
        cauchyContinuityPrincipleToEventFlow x = cauchyContinuityPrincipleToEventFlow y →
          x = y) ∧
      cauchyContinuityPrincipleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyContinuityPrincipleChapterTasteGate⟩
  constructor
  · exact ⟨cauchyContinuityPrincipleFieldFaithful⟩
  constructor
  · exact ⟨cauchyContinuityPrincipleNontrivial⟩
  constructor
  · exact CauchyContinuityPrincipleTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyContinuityPrincipleTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyContinuityPrincipleToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.CauchyContinuityPrincipleUp

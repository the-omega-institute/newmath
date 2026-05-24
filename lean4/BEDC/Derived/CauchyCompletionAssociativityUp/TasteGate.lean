import BEDC.Derived.CauchyCompletionAssociativityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionAssociativityUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyCompletionAssociativityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionAssociativityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionAssociativityEncodeBHist h

def cauchyCompletionAssociativityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionAssociativityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionAssociativityDecodeBHist tail)

private theorem CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionAssociativityDecodeBHist
        (cauchyCompletionAssociativityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionAssociativityFields :
    CauchyCompletionAssociativityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionAssociativityUp.mk M U V I L S R D E F G H C P N =>
      [M, U, V, I, L, S, R, D, E, F, G, H, C, P, N]

def cauchyCompletionAssociativityToEventFlow :
    CauchyCompletionAssociativityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionAssociativityFields x).map
      cauchyCompletionAssociativityEncodeBHist

private def cauchyCompletionAssociativityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionAssociativityEventAt index rest

def cauchyCompletionAssociativityFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionAssociativityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionAssociativityUp.mk
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 0 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 1 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 2 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 3 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 4 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 5 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 6 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 7 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 8 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 9 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 10 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 11 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 12 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 13 ef))
      (cauchyCompletionAssociativityDecodeBHist (cauchyCompletionAssociativityEventAt 14 ef)))

private theorem cauchyCompletionAssociativity_mk_congr
    {M M' U U' V V' I I' L L' S S' R R' D D' E E' F F' G G' H H' C C'
      P P' N N' : BHist}
    (hM : M' = M) (hU : U' = U) (hV : V' = V) (hI : I' = I)
    (hL : L' = L) (hS : S' = S) (hR : R' = R) (hD : D' = D)
    (hE : E' = E) (hF : F' = F) (hG : G' = G) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyCompletionAssociativityUp.mk M' U' V' I' L' S' R' D' E' F' G' H' C' P' N' =
      CauchyCompletionAssociativityUp.mk M U V I L S R D E F G H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hU
  cases hV
  cases hI
  cases hL
  cases hS
  cases hR
  cases hD
  cases hE
  cases hF
  cases hG
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyCompletionAssociativityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionAssociativityUp,
      cauchyCompletionAssociativityFromEventFlow
          (cauchyCompletionAssociativityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M U V I L S R D E F G H C P N =>
      exact
        congrArg some
          (cauchyCompletionAssociativity_mk_congr
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode M)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode U)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode V)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode I)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode L)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode S)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode R)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode D)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode E)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode F)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode G)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode H)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode C)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode P)
            (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode N))

private theorem cauchyCompletionAssociativityToEventFlow_injective
    {x y : CauchyCompletionAssociativityUp} :
    cauchyCompletionAssociativityToEventFlow x =
        cauchyCompletionAssociativityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionAssociativityFromEventFlow
          (cauchyCompletionAssociativityToEventFlow x) =
        cauchyCompletionAssociativityFromEventFlow
          (cauchyCompletionAssociativityToEventFlow y) :=
    congrArg cauchyCompletionAssociativityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionAssociativityTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyCompletionAssociativity_field_faithful :
    ∀ x y : CauchyCompletionAssociativityUp,
      cauchyCompletionAssociativityFields x = cauchyCompletionAssociativityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M U V I L S R D E F G H C P N =>
      cases y with
      | mk M' U' V' I' L' S' R' D' E' F' G' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyCompletionAssociativityBHistCarrier :
    BHistCarrier CauchyCompletionAssociativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionAssociativityToEventFlow
  fromEventFlow := cauchyCompletionAssociativityFromEventFlow

instance cauchyCompletionAssociativityChapterTasteGate :
    ChapterTasteGate CauchyCompletionAssociativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionAssociativityFromEventFlow
          (cauchyCompletionAssociativityToEventFlow x) =
        some x
    exact CauchyCompletionAssociativityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionAssociativityToEventFlow_injective heq)

instance cauchyCompletionAssociativityFieldFaithful :
    FieldFaithful CauchyCompletionAssociativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionAssociativityFields
  field_faithful := cauchyCompletionAssociativity_field_faithful

instance cauchyCompletionAssociativityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletionAssociativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionAssociativityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionAssociativityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionAssociativityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionAssociativityChapterTasteGate

theorem CauchyCompletionAssociativityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionAssociativityUp) ∧
      Nonempty (FieldFaithful CauchyCompletionAssociativityUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyCompletionAssociativityUp) ∧
      (∀ h : BHist,
        cauchyCompletionAssociativityDecodeBHist
          (cauchyCompletionAssociativityEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionAssociativityUp,
        cauchyCompletionAssociativityFromEventFlow
            (cauchyCompletionAssociativityToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCompletionAssociativityUp,
        cauchyCompletionAssociativityToEventFlow x =
            cauchyCompletionAssociativityToEventFlow y →
          x = y) ∧
      cauchyCompletionAssociativityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyCompletionAssociativityChapterTasteGate⟩
  constructor
  · exact ⟨cauchyCompletionAssociativityFieldFaithful⟩
  constructor
  · exact ⟨cauchyCompletionAssociativityNontrivial⟩
  constructor
  · exact CauchyCompletionAssociativityTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyCompletionAssociativityTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyCompletionAssociativityToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.CauchyCompletionAssociativityUp

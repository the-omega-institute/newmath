import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BisectionRootCauchySealUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BisectionRootCauchySealUp : Type where
  | mk (I S M V B W R D E H C P N : BHist) : BisectionRootCauchySealUp
  deriving DecidableEq

def bisectionRootCauchySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bisectionRootCauchySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bisectionRootCauchySealEncodeBHist h

def bisectionRootCauchySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bisectionRootCauchySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bisectionRootCauchySealDecodeBHist tail)

private theorem BisectionRootCauchySealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bisectionRootCauchySealDecodeBHist (bisectionRootCauchySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bisectionRootCauchySealFields : BisectionRootCauchySealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BisectionRootCauchySealUp.mk I S M V B W R D E H C P N =>
      [I, S, M, V, B, W, R, D, E, H, C, P, N]

def bisectionRootCauchySealToEventFlow : BisectionRootCauchySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bisectionRootCauchySealFields x).map bisectionRootCauchySealEncodeBHist

private inductive BisectionRootCauchySealPrefix : Type where
  | mk (I S M V B W R : BHist) (rest : EventFlow) : BisectionRootCauchySealPrefix

private inductive BisectionRootCauchySealSuffix : Type where
  | mk (D E H C P N : BHist) : BisectionRootCauchySealSuffix

private def bisectionRootCauchySealDecodePrefix :
    EventFlow → Option BisectionRootCauchySealPrefix
  -- BEDC touchpoint anchor: BHist BMark
  | I :: restI =>
      match restI with
      | S :: restS =>
          match restS with
          | M :: restM =>
              match restM with
              | V :: restV =>
                  match restV with
                  | B :: restB =>
                      match restB with
                      | W :: restW =>
                          match restW with
                          | R :: restR =>
                              some
                                (BisectionRootCauchySealPrefix.mk
                                  (bisectionRootCauchySealDecodeBHist I)
                                  (bisectionRootCauchySealDecodeBHist S)
                                  (bisectionRootCauchySealDecodeBHist M)
                                  (bisectionRootCauchySealDecodeBHist V)
                                  (bisectionRootCauchySealDecodeBHist B)
                                  (bisectionRootCauchySealDecodeBHist W)
                                  (bisectionRootCauchySealDecodeBHist R)
                                  restR)
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private def bisectionRootCauchySealDecodeSuffix :
    EventFlow → Option BisectionRootCauchySealSuffix
  -- BEDC touchpoint anchor: BHist BMark
  | D :: restD =>
      match restD with
      | E :: restE =>
          match restE with
          | H :: restH =>
              match restH with
              | C :: restC =>
                  match restC with
                  | P :: restP =>
                      match restP with
                      | N :: restN =>
                          match restN with
                          | [] =>
                              some
                                (BisectionRootCauchySealSuffix.mk
                                  (bisectionRootCauchySealDecodeBHist D)
                                  (bisectionRootCauchySealDecodeBHist E)
                                  (bisectionRootCauchySealDecodeBHist H)
                                  (bisectionRootCauchySealDecodeBHist C)
                                  (bisectionRootCauchySealDecodeBHist P)
                                  (bisectionRootCauchySealDecodeBHist N))
                          | _ :: _ => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

def bisectionRootCauchySealFromEventFlow : EventFlow → Option BisectionRootCauchySealUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
    match bisectionRootCauchySealDecodePrefix ef with
    | some (BisectionRootCauchySealPrefix.mk I S M V B W R rest) =>
        match bisectionRootCauchySealDecodeSuffix rest with
        | some (BisectionRootCauchySealSuffix.mk D E H C P N) =>
            some (BisectionRootCauchySealUp.mk I S M V B W R D E H C P N)
        | none => none
    | none => none

private theorem bisectionRootCauchySeal_mk_congr
    {I I' S S' M M' V V' B B' W W' R R' D D' E E' H H' C C' P P' N N' :
      BHist}
    (hI : I' = I) (hS : S' = S) (hM : M' = M) (hV : V' = V)
    (hB : B' = B) (hW : W' = W) (hR : R' = R) (hD : D' = D)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    BisectionRootCauchySealUp.mk I' S' M' V' B' W' R' D' E' H' C' P' N' =
      BisectionRootCauchySealUp.mk I S M V B W R D E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hS
  cases hM
  cases hV
  cases hB
  cases hW
  cases hR
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem BisectionRootCauchySealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BisectionRootCauchySealUp,
      bisectionRootCauchySealFromEventFlow (bisectionRootCauchySealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S M V B W R D E H C P N =>
      exact
        congrArg some
          (bisectionRootCauchySeal_mk_congr
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode I)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode S)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode M)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode V)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode B)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode W)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode R)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode D)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode E)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode H)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode C)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode P)
            (BisectionRootCauchySealTasteGate_single_carrier_alignment_decode N))

private theorem bisectionRootCauchySealToEventFlow_injective
    {x y : BisectionRootCauchySealUp} :
    bisectionRootCauchySealToEventFlow x = bisectionRootCauchySealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bisectionRootCauchySealFromEventFlow (bisectionRootCauchySealToEventFlow x) =
        bisectionRootCauchySealFromEventFlow (bisectionRootCauchySealToEventFlow y) :=
    congrArg bisectionRootCauchySealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BisectionRootCauchySealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BisectionRootCauchySealTasteGate_single_carrier_alignment_round_trip y)))

private theorem bisectionRootCauchySeal_field_faithful :
    ∀ x y : BisectionRootCauchySealUp,
      bisectionRootCauchySealFields x = bisectionRootCauchySealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ S₁ M₁ V₁ B₁ W₁ R₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ S₂ M₂ V₂ B₂ W₂ R₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bisectionRootCauchySealBHistCarrier : BHistCarrier BisectionRootCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bisectionRootCauchySealToEventFlow
  fromEventFlow := bisectionRootCauchySealFromEventFlow

instance bisectionRootCauchySealChapterTasteGate :
    ChapterTasteGate BisectionRootCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bisectionRootCauchySealFromEventFlow (bisectionRootCauchySealToEventFlow x) =
      some x
    exact BisectionRootCauchySealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bisectionRootCauchySealToEventFlow_injective heq)

instance bisectionRootCauchySealFieldFaithful : FieldFaithful BisectionRootCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bisectionRootCauchySealFields
  field_faithful := bisectionRootCauchySeal_field_faithful

instance bisectionRootCauchySealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BisectionRootCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BisectionRootCauchySealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BisectionRootCauchySealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BisectionRootCauchySealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bisectionRootCauchySealChapterTasteGate

theorem BisectionRootCauchySealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BisectionRootCauchySealUp) ∧
      Nonempty (FieldFaithful BisectionRootCauchySealUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BisectionRootCauchySealUp) ∧
      (∀ h : BHist,
        bisectionRootCauchySealDecodeBHist (bisectionRootCauchySealEncodeBHist h) = h) ∧
      (∀ x : BisectionRootCauchySealUp,
        bisectionRootCauchySealFromEventFlow (bisectionRootCauchySealToEventFlow x) =
          some x) ∧
      (∀ x y : BisectionRootCauchySealUp,
        bisectionRootCauchySealToEventFlow x = bisectionRootCauchySealToEventFlow y ->
          x = y) ∧
      bisectionRootCauchySealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨bisectionRootCauchySealChapterTasteGate⟩
  constructor
  · exact ⟨bisectionRootCauchySealFieldFaithful⟩
  constructor
  · exact ⟨bisectionRootCauchySealNontrivial⟩
  constructor
  · exact BisectionRootCauchySealTasteGate_single_carrier_alignment_decode
  constructor
  · exact BisectionRootCauchySealTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact bisectionRootCauchySealToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.BisectionRootCauchySealUp

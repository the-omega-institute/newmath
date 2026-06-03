import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetDerivativeUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetDerivativeUp : Type where
  | mk (X A L R H C P N : BHist) : FrechetDerivativeUp
  deriving DecidableEq

def frechetDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetDerivativeEncodeBHist h

def frechetDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetDerivativeDecodeBHist tail)

private theorem FrechetDerivativeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, frechetDerivativeDecodeBHist (frechetDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frechetDerivativeFields : FrechetDerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetDerivativeUp.mk X A L R H C P N => [X, A, L, R, H, C, P, N]

def frechetDerivativeToEventFlow : FrechetDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (frechetDerivativeFields x).map frechetDerivativeEncodeBHist

def frechetDerivativeFromEventFlow : EventFlow → Option FrechetDerivativeUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | A :: restA =>
          match restA with
          | L :: restL =>
              match restL with
              | R :: restR =>
                  match restR with
                  | H :: restH =>
                      match restH with
                      | C :: restC =>
                          match restC with
                          | P :: restP =>
                              match restP with
                              | N :: rest =>
                                  match rest with
                                  | [] =>
                                      some
                                        (FrechetDerivativeUp.mk
                                          (frechetDerivativeDecodeBHist X)
                                          (frechetDerivativeDecodeBHist A)
                                          (frechetDerivativeDecodeBHist L)
                                          (frechetDerivativeDecodeBHist R)
                                          (frechetDerivativeDecodeBHist H)
                                          (frechetDerivativeDecodeBHist C)
                                          (frechetDerivativeDecodeBHist P)
                                          (frechetDerivativeDecodeBHist N))
                                  | _ :: _ => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem frechetDerivative_mk_congr
    {X X' A A' L L' R R' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hA : A' = A) (hL : L' = L) (hR : R' = R)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    FrechetDerivativeUp.mk X' A' L' R' H' C' P' N' =
      FrechetDerivativeUp.mk X A L R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hA
  cases hL
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem FrechetDerivativeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FrechetDerivativeUp,
      frechetDerivativeFromEventFlow (frechetDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A L R H C P N =>
      exact
        congrArg some
          (frechetDerivative_mk_congr
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode X)
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode A)
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode L)
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode R)
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode H)
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode C)
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode P)
            (FrechetDerivativeTasteGate_single_carrier_alignment_decode N))

private theorem frechetDerivativeToEventFlow_injective {x y : FrechetDerivativeUp} :
    frechetDerivativeToEventFlow x = frechetDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetDerivativeFromEventFlow (frechetDerivativeToEventFlow x) =
        frechetDerivativeFromEventFlow (frechetDerivativeToEventFlow y) :=
    congrArg frechetDerivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrechetDerivativeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrechetDerivativeTasteGate_single_carrier_alignment_round_trip y)))

private theorem frechetDerivative_field_faithful :
    ∀ x y : FrechetDerivativeUp, frechetDerivativeFields x = frechetDerivativeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X A L R H C P N =>
      cases y with
      | mk X' A' L' R' H' C' P' N' =>
          cases hfields
          rfl

instance frechetDerivativeBHistCarrier : BHistCarrier FrechetDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetDerivativeToEventFlow
  fromEventFlow := frechetDerivativeFromEventFlow

instance frechetDerivativeChapterTasteGate : ChapterTasteGate FrechetDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetDerivativeFromEventFlow (frechetDerivativeToEventFlow x) = some x
    exact FrechetDerivativeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (frechetDerivativeToEventFlow_injective heq)

instance frechetDerivativeFieldFaithful : FieldFaithful FrechetDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := frechetDerivativeFields
  field_faithful := frechetDerivative_field_faithful

instance frechetDerivativeNontrivial : BEDC.Meta.TasteGate.Nontrivial FrechetDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FrechetDerivativeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FrechetDerivativeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FrechetDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frechetDerivativeChapterTasteGate

theorem FrechetDerivativeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FrechetDerivativeUp) ∧
      Nonempty (FieldFaithful FrechetDerivativeUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial FrechetDerivativeUp) ∧
      (∀ h : BHist,
        frechetDerivativeDecodeBHist (frechetDerivativeEncodeBHist h) = h) ∧
      (∀ x : FrechetDerivativeUp,
        frechetDerivativeFromEventFlow (frechetDerivativeToEventFlow x) = some x) ∧
      (∀ x y : FrechetDerivativeUp,
        frechetDerivativeToEventFlow x = frechetDerivativeToEventFlow y -> x = y) ∧
      frechetDerivativeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨frechetDerivativeChapterTasteGate⟩
  constructor
  · exact ⟨frechetDerivativeFieldFaithful⟩
  constructor
  · exact ⟨frechetDerivativeNontrivial⟩
  constructor
  · exact FrechetDerivativeTasteGate_single_carrier_alignment_decode
  constructor
  · exact FrechetDerivativeTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact frechetDerivativeToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.FrechetDerivativeUp

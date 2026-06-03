import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpperRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpperRealUp : Type where
  | mk (U0 L W R E H C P N : BHist) : UpperRealUp
  deriving DecidableEq

def upperRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upperRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upperRealEncodeBHist h

def upperRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upperRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upperRealDecodeBHist tail)

private theorem UpperRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, upperRealDecodeBHist (upperRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def upperRealFields : UpperRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpperRealUp.mk U0 L W R E H C P N => [U0, L, W, R, E, H, C, P, N]

def upperRealToEventFlow : UpperRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (upperRealFields x).map upperRealEncodeBHist

def upperRealFromEventFlow : EventFlow → Option UpperRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | U0 :: restU0 =>
      match restU0 with
      | L :: restL =>
          match restL with
          | W :: restW =>
              match restW with
              | R :: restR =>
                  match restR with
                  | E :: restE =>
                      match restE with
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
                                            (UpperRealUp.mk
                                              (upperRealDecodeBHist U0)
                                              (upperRealDecodeBHist L)
                                              (upperRealDecodeBHist W)
                                              (upperRealDecodeBHist R)
                                              (upperRealDecodeBHist E)
                                              (upperRealDecodeBHist H)
                                              (upperRealDecodeBHist C)
                                              (upperRealDecodeBHist P)
                                              (upperRealDecodeBHist N))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem upperReal_mk_congr
    {U0 U0' L L' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hU0 : U0' = U0) (hL : L' = L) (hW : W' = W) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    UpperRealUp.mk U0' L' W' R' E' H' C' P' N' =
      UpperRealUp.mk U0 L W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hU0
  cases hL
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem UpperRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UpperRealUp, upperRealFromEventFlow (upperRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U0 L W R E H C P N =>
      exact
        congrArg some
          (upperReal_mk_congr
            (UpperRealTasteGate_single_carrier_alignment_decode U0)
            (UpperRealTasteGate_single_carrier_alignment_decode L)
            (UpperRealTasteGate_single_carrier_alignment_decode W)
            (UpperRealTasteGate_single_carrier_alignment_decode R)
            (UpperRealTasteGate_single_carrier_alignment_decode E)
            (UpperRealTasteGate_single_carrier_alignment_decode H)
            (UpperRealTasteGate_single_carrier_alignment_decode C)
            (UpperRealTasteGate_single_carrier_alignment_decode P)
            (UpperRealTasteGate_single_carrier_alignment_decode N))

private theorem upperRealToEventFlow_injective {x y : UpperRealUp} :
    upperRealToEventFlow x = upperRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upperRealFromEventFlow (upperRealToEventFlow x) =
        upperRealFromEventFlow (upperRealToEventFlow y) :=
    congrArg upperRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UpperRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UpperRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem upperReal_field_faithful :
    ∀ x y : UpperRealUp, upperRealFields x = upperRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U0 L W R E H C P N =>
      cases y with
      | mk U0' L' W' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance upperRealBHistCarrier : BHistCarrier UpperRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upperRealToEventFlow
  fromEventFlow := upperRealFromEventFlow

instance upperRealChapterTasteGate : ChapterTasteGate UpperRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upperRealFromEventFlow (upperRealToEventFlow x) = some x
    exact UpperRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upperRealToEventFlow_injective heq)

instance upperRealFieldFaithful : FieldFaithful UpperRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := upperRealFields
  field_faithful := upperReal_field_faithful

instance upperRealNontrivial : BEDC.Meta.TasteGate.Nontrivial UpperRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpperRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpperRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UpperRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UpperRealUp) ∧
      Nonempty (FieldFaithful UpperRealUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial UpperRealUp) ∧
      (∀ h : BHist, upperRealDecodeBHist (upperRealEncodeBHist h) = h) ∧
      (∀ x : UpperRealUp, upperRealFromEventFlow (upperRealToEventFlow x) = some x) ∧
      upperRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨upperRealChapterTasteGate⟩
  constructor
  · exact ⟨upperRealFieldFaithful⟩
  constructor
  · exact ⟨upperRealNontrivial⟩
  constructor
  · exact UpperRealTasteGate_single_carrier_alignment_decode
  constructor
  · exact UpperRealTasteGate_single_carrier_alignment_round_trip
  · rfl

end BEDC.Derived.UpperRealUp

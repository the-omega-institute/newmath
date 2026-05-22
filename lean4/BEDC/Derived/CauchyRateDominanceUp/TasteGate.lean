import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateDominanceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRateDominanceUp : Type where
  | mk (M D S Q E H C P N : BHist) : CauchyRateDominanceUp
  deriving DecidableEq

def cauchyRateDominanceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateDominanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateDominanceEncodeBHist h

def cauchyRateDominanceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateDominanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateDominanceDecodeBHist tail)

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_decode :
    forall h : BHist, cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRateDominanceFields : CauchyRateDominanceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateDominanceUp.mk M D S Q E H C P N => [M, D, S, Q, E, H, C, P, N]

def cauchyRateDominanceToEventFlow : CauchyRateDominanceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRateDominanceFields x).map cauchyRateDominanceEncodeBHist

def cauchyRateDominanceFromEventFlow : EventFlow -> Option CauchyRateDominanceUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | D :: restD =>
          match restD with
          | S :: restS =>
              match restS with
              | Q :: restQ =>
                  match restQ with
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
                                            (CauchyRateDominanceUp.mk
                                              (cauchyRateDominanceDecodeBHist M)
                                              (cauchyRateDominanceDecodeBHist D)
                                              (cauchyRateDominanceDecodeBHist S)
                                              (cauchyRateDominanceDecodeBHist Q)
                                              (cauchyRateDominanceDecodeBHist E)
                                              (cauchyRateDominanceDecodeBHist H)
                                              (cauchyRateDominanceDecodeBHist C)
                                              (cauchyRateDominanceDecodeBHist P)
                                              (cauchyRateDominanceDecodeBHist N))
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

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_mk_congr
    {M M' D D' S S' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hD : D' = D) (hS : S' = S) (hQ : Q' = Q)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    CauchyRateDominanceUp.mk M' D' S' Q' E' H' C' P' N' =
      CauchyRateDominanceUp.mk M D S Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hD
  cases hS
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyRateDominanceUp,
      cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D S Q E H C P N =>
      exact
        congrArg some
          (CauchyRateDominanceTasteGate_single_carrier_alignment_mk_congr
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode M)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode D)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode S)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode Q)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode E)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode H)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode C)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode P)
            (CauchyRateDominanceTasteGate_single_carrier_alignment_decode N))

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRateDominanceUp} :
    cauchyRateDominanceToEventFlow x = cauchyRateDominanceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow x) =
        cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow y) :=
    congrArg cauchyRateDominanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRateDominanceBHistCarrier : BHistCarrier CauchyRateDominanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateDominanceToEventFlow
  fromEventFlow := cauchyRateDominanceFromEventFlow

instance cauchyRateDominanceChapterTasteGate : ChapterTasteGate CauchyRateDominanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow x) = some x
    exact CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRateDominanceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyRateDominanceTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist h) = h) ∧
      (forall x : CauchyRateDominanceUp,
        cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow x) = some x) ∧
        (forall x y : CauchyRateDominanceUp,
          cauchyRateDominanceToEventFlow x = cauchyRateDominanceToEventFlow y -> x = y) ∧
          cauchyRateDominanceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyRateDominanceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyRateDominanceTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyRateDominanceUp

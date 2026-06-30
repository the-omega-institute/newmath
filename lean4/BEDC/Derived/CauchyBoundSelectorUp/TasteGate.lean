import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyBoundSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyBoundSelectorUp : Type where
  | mk (S Q D R I W E H C P N : BHist) : CauchyBoundSelectorUp
  deriving DecidableEq

def cauchyBoundSelectorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyBoundSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyBoundSelectorEncodeBHist h

def cauchyBoundSelectorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyBoundSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyBoundSelectorDecodeBHist tail)

private theorem CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      cauchyBoundSelectorDecodeBHist (cauchyBoundSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyBoundSelectorFields : CauchyBoundSelectorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyBoundSelectorUp.mk S Q D R I W E H C P N =>
      [S, Q, D, R, I, W, E, H, C, P, N]

def cauchyBoundSelectorToEventFlow : CauchyBoundSelectorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyBoundSelectorFields x).map cauchyBoundSelectorEncodeBHist

def cauchyBoundSelectorFromEventFlow : EventFlow -> Option CauchyBoundSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | Q :: restQ =>
          match restQ with
          | D :: restD =>
              match restD with
              | R :: restR =>
                  match restR with
                  | I :: restI =>
                      match restI with
                      | W :: restW =>
                          match restW with
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
                                                    (CauchyBoundSelectorUp.mk
                                                      (cauchyBoundSelectorDecodeBHist S)
                                                      (cauchyBoundSelectorDecodeBHist Q)
                                                      (cauchyBoundSelectorDecodeBHist D)
                                                      (cauchyBoundSelectorDecodeBHist R)
                                                      (cauchyBoundSelectorDecodeBHist I)
                                                      (cauchyBoundSelectorDecodeBHist W)
                                                      (cauchyBoundSelectorDecodeBHist E)
                                                      (cauchyBoundSelectorDecodeBHist H)
                                                      (cauchyBoundSelectorDecodeBHist C)
                                                      (cauchyBoundSelectorDecodeBHist P)
                                                      (cauchyBoundSelectorDecodeBHist N))
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
      | [] => none
  | [] => none

private theorem CauchyBoundSelectorTasteGate_single_carrier_alignment_mk_congr
    {S S' Q Q' D D' R R' I I' W W' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hQ : Q' = Q) (hD : D' = D) (hR : R' = R)
    (hI : I' = I) (hW : W' = W) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyBoundSelectorUp.mk S' Q' D' R' I' W' E' H' C' P' N' =
      CauchyBoundSelectorUp.mk S Q D R I W E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hQ
  cases hD
  cases hR
  cases hI
  cases hW
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyBoundSelectorTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyBoundSelectorUp,
      cauchyBoundSelectorFromEventFlow (cauchyBoundSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D R I W E H C P N =>
      exact
        congrArg some
          (CauchyBoundSelectorTasteGate_single_carrier_alignment_mk_congr
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode S)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode Q)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode D)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode R)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode I)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode W)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode E)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode H)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode C)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode P)
            (CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode N))

private theorem CauchyBoundSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyBoundSelectorUp} :
    cauchyBoundSelectorToEventFlow x = cauchyBoundSelectorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyBoundSelectorFromEventFlow (cauchyBoundSelectorToEventFlow x) =
        cauchyBoundSelectorFromEventFlow (cauchyBoundSelectorToEventFlow y) :=
    congrArg cauchyBoundSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyBoundSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyBoundSelectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyBoundSelectorTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : CauchyBoundSelectorUp,
      cauchyBoundSelectorFields x = cauchyBoundSelectorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S Q D R I W E H C P N =>
      cases y with
      | mk S' Q' D' R' I' W' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyBoundSelectorBHistCarrier : BHistCarrier CauchyBoundSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyBoundSelectorToEventFlow
  fromEventFlow := cauchyBoundSelectorFromEventFlow

instance cauchyBoundSelectorChapterTasteGate : ChapterTasteGate CauchyBoundSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyBoundSelectorFromEventFlow (cauchyBoundSelectorToEventFlow x) = some x
    exact CauchyBoundSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyBoundSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyBoundSelectorFieldFaithful : FieldFaithful CauchyBoundSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyBoundSelectorFields
  field_faithful := CauchyBoundSelectorTasteGate_single_carrier_alignment_fields_faithful

instance cauchyBoundSelectorNontrivial : Nontrivial CauchyBoundSelectorUp where
  witness_pair :=
    ⟨CauchyBoundSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyBoundSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyBoundSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyBoundSelectorChapterTasteGate

theorem CauchyBoundSelectorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyBoundSelectorUp) ∧
      Nonempty (FieldFaithful CauchyBoundSelectorUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyBoundSelectorUp) ∧
          (forall h : BHist,
            cauchyBoundSelectorDecodeBHist (cauchyBoundSelectorEncodeBHist h) = h) ∧
            (forall x : CauchyBoundSelectorUp,
              cauchyBoundSelectorFromEventFlow (cauchyBoundSelectorToEventFlow x) =
                some x) ∧
              cauchyBoundSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyBoundSelectorChapterTasteGate⟩,
      ⟨cauchyBoundSelectorFieldFaithful⟩,
      ⟨cauchyBoundSelectorNontrivial⟩,
      CauchyBoundSelectorTasteGate_single_carrier_alignment_decode_encode,
      CauchyBoundSelectorTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchyBoundSelectorUp

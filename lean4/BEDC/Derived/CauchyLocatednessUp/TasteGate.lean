import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyLocatednessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyLocatednessUp : Type where
  | mk (R W D Q V H C P N : BHist) : CauchyLocatednessUp
  deriving DecidableEq

def cauchyLocatednessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyLocatednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyLocatednessEncodeBHist h

def cauchyLocatednessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyLocatednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyLocatednessDecodeBHist tail)

private theorem CauchyLocatednessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CauchyLocatednessTasteGate_single_carrier_alignment_mk_congr
    {R R' W W' D D' Q Q' V V' H H' C C' P P' N N' : BHist}
    (hR : R = R') (hW : W = W') (hD : D = D') (hQ : Q = Q') (hV : V = V')
    (hH : H = H') (hC : C = C') (hP : P = P') (hN : N = N') :
    CauchyLocatednessUp.mk R W D Q V H C P N =
      CauchyLocatednessUp.mk R' W' D' Q' V' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hW
  cases hD
  cases hQ
  cases hV
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyLocatednessToEventFlow : CauchyLocatednessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyLocatednessUp.mk R W D Q V H C P N =>
      [cauchyLocatednessEncodeBHist R,
        cauchyLocatednessEncodeBHist W,
        cauchyLocatednessEncodeBHist D,
        cauchyLocatednessEncodeBHist Q,
        cauchyLocatednessEncodeBHist V,
        cauchyLocatednessEncodeBHist H,
        cauchyLocatednessEncodeBHist C,
        cauchyLocatednessEncodeBHist P,
        cauchyLocatednessEncodeBHist N]

def cauchyLocatednessFromEventFlow (ef : EventFlow) : Option CauchyLocatednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | R :: restR =>
      match restR with
      | [] => none
      | W :: restW =>
          match restW with
          | [] => none
          | D :: restD =>
              match restD with
              | [] => none
              | Q :: restQ =>
                  match restQ with
                  | [] => none
                  | V :: restV =>
                      match restV with
                      | [] => none
                      | H :: restH =>
                          match restH with
                          | [] => none
                          | C :: restC =>
                              match restC with
                              | [] => none
                              | P :: restP =>
                                  match restP with
                                  | [] => none
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (CauchyLocatednessUp.mk
                                              (cauchyLocatednessDecodeBHist R)
                                              (cauchyLocatednessDecodeBHist W)
                                              (cauchyLocatednessDecodeBHist D)
                                              (cauchyLocatednessDecodeBHist Q)
                                              (cauchyLocatednessDecodeBHist V)
                                              (cauchyLocatednessDecodeBHist H)
                                              (cauchyLocatednessDecodeBHist C)
                                              (cauchyLocatednessDecodeBHist P)
                                              (cauchyLocatednessDecodeBHist N))
                                      | _ :: _ => none

private theorem CauchyLocatednessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyLocatednessUp,
      cauchyLocatednessFromEventFlow (cauchyLocatednessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D Q V H C P N =>
      change
        some
          (CauchyLocatednessUp.mk
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist R))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist W))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist D))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist Q))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist V))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist H))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist C))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist P))
            (cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist N))) =
          some (CauchyLocatednessUp.mk R W D Q V H C P N)
      exact congrArg some
        (CauchyLocatednessTasteGate_single_carrier_alignment_mk_congr
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode R)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode W)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode D)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode Q)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode V)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode H)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode C)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode P)
          (CauchyLocatednessTasteGate_single_carrier_alignment_decode N))

private theorem CauchyLocatednessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyLocatednessUp} :
    cauchyLocatednessToEventFlow x = cauchyLocatednessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyLocatednessFromEventFlow (cauchyLocatednessToEventFlow x) =
        cauchyLocatednessFromEventFlow (cauchyLocatednessToEventFlow y) :=
    congrArg cauchyLocatednessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyLocatednessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyLocatednessTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyLocatednessBHistCarrier : BHistCarrier CauchyLocatednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyLocatednessToEventFlow
  fromEventFlow := cauchyLocatednessFromEventFlow

instance cauchyLocatednessChapterTasteGate :
    ChapterTasteGate CauchyLocatednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyLocatednessFromEventFlow (cauchyLocatednessToEventFlow x) = some x
    exact CauchyLocatednessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyLocatednessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyLocatednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyLocatednessChapterTasteGate

theorem CauchyLocatednessTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyLocatednessDecodeBHist (cauchyLocatednessEncodeBHist h) = h) ∧
      (∀ x : CauchyLocatednessUp,
        cauchyLocatednessFromEventFlow (cauchyLocatednessToEventFlow x) = some x) ∧
        (∀ x y : CauchyLocatednessUp,
          cauchyLocatednessToEventFlow x = cauchyLocatednessToEventFlow y → x = y) ∧
          cauchyLocatednessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyLocatednessTasteGate_single_carrier_alignment_decode,
      CauchyLocatednessTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyLocatednessTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyLocatednessUp

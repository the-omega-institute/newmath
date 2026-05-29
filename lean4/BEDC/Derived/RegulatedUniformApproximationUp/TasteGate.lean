import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedUniformApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedUniformApproximationUp : Type where
  | mk (I A T U E H C P N : BHist) : RegulatedUniformApproximationUp
  deriving DecidableEq

def regulatedUniformApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedUniformApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedUniformApproximationEncodeBHist h

def regulatedUniformApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedUniformApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedUniformApproximationDecodeBHist tail)

private theorem RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regulatedUniformApproximationDecodeBHist
        (regulatedUniformApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RegulatedUniformApproximationTasteGate_single_carrier_alignment_mk_congr
    {I I' A A' T T' U U' E E' H H' C C' P P' N N' : BHist}
    (hI : I = I') (hA : A = A') (hT : T = T') (hU : U = U') (hE : E = E')
    (hH : H = H') (hC : C = C') (hP : P = P') (hN : N = N') :
    RegulatedUniformApproximationUp.mk I A T U E H C P N =
      RegulatedUniformApproximationUp.mk I' A' T' U' E' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hA
  cases hT
  cases hU
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regulatedUniformApproximationToEventFlow :
    RegulatedUniformApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedUniformApproximationUp.mk I A T U E H C P N =>
      [regulatedUniformApproximationEncodeBHist I,
        regulatedUniformApproximationEncodeBHist A,
        regulatedUniformApproximationEncodeBHist T,
        regulatedUniformApproximationEncodeBHist U,
        regulatedUniformApproximationEncodeBHist E,
        regulatedUniformApproximationEncodeBHist H,
        regulatedUniformApproximationEncodeBHist C,
        regulatedUniformApproximationEncodeBHist P,
        regulatedUniformApproximationEncodeBHist N]

def regulatedUniformApproximationFromEventFlow
    (ef : EventFlow) : Option RegulatedUniformApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | I :: restI =>
      match restI with
      | [] => none
      | A :: restA =>
          match restA with
          | [] => none
          | T :: restT =>
              match restT with
              | [] => none
              | U :: restU =>
                  match restU with
                  | [] => none
                  | E :: restE =>
                      match restE with
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
                                            (RegulatedUniformApproximationUp.mk
                                              (regulatedUniformApproximationDecodeBHist I)
                                              (regulatedUniformApproximationDecodeBHist A)
                                              (regulatedUniformApproximationDecodeBHist T)
                                              (regulatedUniformApproximationDecodeBHist U)
                                              (regulatedUniformApproximationDecodeBHist E)
                                              (regulatedUniformApproximationDecodeBHist H)
                                              (regulatedUniformApproximationDecodeBHist C)
                                              (regulatedUniformApproximationDecodeBHist P)
                                              (regulatedUniformApproximationDecodeBHist N))
                                      | _ :: _ => none

private theorem RegulatedUniformApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegulatedUniformApproximationUp,
      regulatedUniformApproximationFromEventFlow
        (regulatedUniformApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I A T U E H C P N =>
      change
        some
          (RegulatedUniformApproximationUp.mk
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist I))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist A))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist T))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist U))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist E))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist H))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist C))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist P))
            (regulatedUniformApproximationDecodeBHist
              (regulatedUniformApproximationEncodeBHist N))) =
          some (RegulatedUniformApproximationUp.mk I A T U E H C P N)
      exact congrArg some
        (RegulatedUniformApproximationTasteGate_single_carrier_alignment_mk_congr
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode I)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode A)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode T)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode U)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode E)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode H)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode C)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode P)
          (RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode N))

private theorem RegulatedUniformApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedUniformApproximationUp} :
    regulatedUniformApproximationToEventFlow x =
      regulatedUniformApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedUniformApproximationFromEventFlow
          (regulatedUniformApproximationToEventFlow x) =
        regulatedUniformApproximationFromEventFlow
          (regulatedUniformApproximationToEventFlow y) :=
    congrArg regulatedUniformApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegulatedUniformApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegulatedUniformApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedUniformApproximationBHistCarrier :
    BHistCarrier RegulatedUniformApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedUniformApproximationToEventFlow
  fromEventFlow := regulatedUniformApproximationFromEventFlow

instance regulatedUniformApproximationChapterTasteGate :
    ChapterTasteGate RegulatedUniformApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regulatedUniformApproximationFromEventFlow
        (regulatedUniformApproximationToEventFlow x) = some x
    exact RegulatedUniformApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegulatedUniformApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegulatedUniformApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedUniformApproximationChapterTasteGate

theorem RegulatedUniformApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regulatedUniformApproximationDecodeBHist
        (regulatedUniformApproximationEncodeBHist h) = h) ∧
      (∀ x : RegulatedUniformApproximationUp,
        regulatedUniformApproximationFromEventFlow
          (regulatedUniformApproximationToEventFlow x) = some x) ∧
        (∀ x y : RegulatedUniformApproximationUp,
          regulatedUniformApproximationToEventFlow x =
            regulatedUniformApproximationToEventFlow y → x = y) ∧
          regulatedUniformApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegulatedUniformApproximationTasteGate_single_carrier_alignment_decode,
      RegulatedUniformApproximationTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RegulatedUniformApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegulatedUniformApproximationUp

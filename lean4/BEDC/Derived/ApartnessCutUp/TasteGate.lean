import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApartnessCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApartnessCutUp : Type where
  | mk (L U K S R D E Q H C P N : BHist) : ApartnessCutUp
  deriving DecidableEq

def apartnessCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apartnessCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apartnessCutEncodeBHist h

def apartnessCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apartnessCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apartnessCutDecodeBHist tail)

private theorem ApartnessCutTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, apartnessCutDecodeBHist (apartnessCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apartnessCutFields : ApartnessCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApartnessCutUp.mk L U K S R D E Q H C P N => [L, U, K, S, R, D, E, Q, H, C, P, N]

def apartnessCutToEventFlow : ApartnessCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (apartnessCutFields x).map apartnessCutEncodeBHist

def apartnessCutFromEventFlow : EventFlow → Option ApartnessCutUp
  -- BEDC touchpoint anchor: BHist BMark
  | L :: restL =>
      match restL with
      | U :: restU =>
          match restU with
          | K :: restK =>
              match restK with
              | S :: restS =>
                  match restS with
                  | R :: restR =>
                      match restR with
                      | D :: restD =>
                          match restD with
                          | E :: restE =>
                              match restE with
                              | Q :: restQ =>
                                  match restQ with
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
                                                        (ApartnessCutUp.mk
                                                          (apartnessCutDecodeBHist L)
                                                          (apartnessCutDecodeBHist U)
                                                          (apartnessCutDecodeBHist K)
                                                          (apartnessCutDecodeBHist S)
                                                          (apartnessCutDecodeBHist R)
                                                          (apartnessCutDecodeBHist D)
                                                          (apartnessCutDecodeBHist E)
                                                          (apartnessCutDecodeBHist Q)
                                                          (apartnessCutDecodeBHist H)
                                                          (apartnessCutDecodeBHist C)
                                                          (apartnessCutDecodeBHist P)
                                                          (apartnessCutDecodeBHist N))
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
  | [] => none

private theorem apartnessCut_mk_congr
    {L L' U U' K K' S S' R R' D D' E E' Q Q' H H' C C' P P' N N' : BHist}
    (hL : L' = L) (hU : U' = U) (hK : K' = K) (hS : S' = S)
    (hR : R' = R) (hD : D' = D) (hE : E' = E) (hQ : Q' = Q)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ApartnessCutUp.mk L' U' K' S' R' D' E' Q' H' C' P' N' =
      ApartnessCutUp.mk L U K S R D E Q H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hU
  cases hK
  cases hS
  cases hR
  cases hD
  cases hE
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem ApartnessCutTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ApartnessCutUp,
      apartnessCutFromEventFlow (apartnessCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U K S R D E Q H C P N =>
      exact
        congrArg some
          (apartnessCut_mk_congr
            (ApartnessCutTasteGate_single_carrier_alignment_decode L)
            (ApartnessCutTasteGate_single_carrier_alignment_decode U)
            (ApartnessCutTasteGate_single_carrier_alignment_decode K)
            (ApartnessCutTasteGate_single_carrier_alignment_decode S)
            (ApartnessCutTasteGate_single_carrier_alignment_decode R)
            (ApartnessCutTasteGate_single_carrier_alignment_decode D)
            (ApartnessCutTasteGate_single_carrier_alignment_decode E)
            (ApartnessCutTasteGate_single_carrier_alignment_decode Q)
            (ApartnessCutTasteGate_single_carrier_alignment_decode H)
            (ApartnessCutTasteGate_single_carrier_alignment_decode C)
            (ApartnessCutTasteGate_single_carrier_alignment_decode P)
            (ApartnessCutTasteGate_single_carrier_alignment_decode N))

private theorem apartnessCutToEventFlow_injective
    {x y : ApartnessCutUp} :
    apartnessCutToEventFlow x = apartnessCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apartnessCutFromEventFlow (apartnessCutToEventFlow x) =
        apartnessCutFromEventFlow (apartnessCutToEventFlow y) :=
    congrArg apartnessCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ApartnessCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ApartnessCutTasteGate_single_carrier_alignment_round_trip y)))

instance apartnessCutBHistCarrier : BHistCarrier ApartnessCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apartnessCutToEventFlow
  fromEventFlow := apartnessCutFromEventFlow

instance apartnessCutChapterTasteGate : ChapterTasteGate ApartnessCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apartnessCutFromEventFlow (apartnessCutToEventFlow x) = some x
    exact ApartnessCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apartnessCutToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ApartnessCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apartnessCutChapterTasteGate

theorem ApartnessCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, apartnessCutDecodeBHist (apartnessCutEncodeBHist h) = h) ∧
      (∀ x : ApartnessCutUp, apartnessCutFromEventFlow (apartnessCutToEventFlow x) = some x) ∧
      (∀ x y : ApartnessCutUp, apartnessCutToEventFlow x = apartnessCutToEventFlow y → x = y) ∧
      apartnessCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · intro x
    exact ApartnessCutTasteGate_single_carrier_alignment_round_trip x
  constructor
  · intro x y heq
    have hread :
        apartnessCutFromEventFlow (apartnessCutToEventFlow x) =
          apartnessCutFromEventFlow (apartnessCutToEventFlow y) :=
      congrArg apartnessCutFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (ApartnessCutTasteGate_single_carrier_alignment_round_trip x).symm
        (Eq.trans hread
          (ApartnessCutTasteGate_single_carrier_alignment_round_trip y)))
  · rfl

end BEDC.Derived.ApartnessCutUp

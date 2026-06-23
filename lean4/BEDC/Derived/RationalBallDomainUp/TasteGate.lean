import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalBallDomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalBallDomainUp : Type where
  | mk (B K F O S R E H C P N : BHist) : RationalBallDomainUp
  deriving DecidableEq

def rationalBallDomainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalBallDomainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalBallDomainEncodeBHist h

def rationalBallDomainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalBallDomainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalBallDomainDecodeBHist tail)

private theorem RationalBallDomainTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      rationalBallDomainDecodeBHist (rationalBallDomainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalBallDomainFields : RationalBallDomainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalBallDomainUp.mk B K F O S R E H C P N => [B, K, F, O, S, R, E, H, C, P, N]

def rationalBallDomainToEventFlow : RationalBallDomainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalBallDomainFields x).map rationalBallDomainEncodeBHist

def rationalBallDomainFromEventFlow : EventFlow → Option RationalBallDomainUp
  -- BEDC touchpoint anchor: BHist BMark
  | B :: restB =>
      match restB with
      | K :: restK =>
          match restK with
          | F :: restF =>
              match restF with
              | O :: restO =>
                  match restO with
                  | S :: restS =>
                      match restS with
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
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (RationalBallDomainUp.mk
                                                      (rationalBallDomainDecodeBHist B)
                                                      (rationalBallDomainDecodeBHist K)
                                                      (rationalBallDomainDecodeBHist F)
                                                      (rationalBallDomainDecodeBHist O)
                                                      (rationalBallDomainDecodeBHist S)
                                                      (rationalBallDomainDecodeBHist R)
                                                      (rationalBallDomainDecodeBHist E)
                                                      (rationalBallDomainDecodeBHist H)
                                                      (rationalBallDomainDecodeBHist C)
                                                      (rationalBallDomainDecodeBHist P)
                                                      (rationalBallDomainDecodeBHist N))
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

private theorem rationalBallDomain_mk_congr
    {B B' K K' F F' O O' S S' R R' E E' H H' C C' P P' N N' : BHist}
    (hB : B' = B) (hK : K' = K) (hF : F' = F) (hO : O' = O)
    (hS : S' = S) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RationalBallDomainUp.mk B' K' F' O' S' R' E' H' C' P' N' =
      RationalBallDomainUp.mk B K F O S R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hK
  cases hF
  cases hO
  cases hS
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RationalBallDomainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RationalBallDomainUp,
      rationalBallDomainFromEventFlow (rationalBallDomainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B K F O S R E H C P N =>
      exact
        congrArg some
          (rationalBallDomain_mk_congr
            (RationalBallDomainTasteGate_single_carrier_alignment_decode B)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode K)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode F)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode O)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode S)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode R)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode E)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode H)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode C)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode P)
            (RationalBallDomainTasteGate_single_carrier_alignment_decode N))

private theorem rationalBallDomainToEventFlow_injective
    {x y : RationalBallDomainUp} :
    rationalBallDomainToEventFlow x = rationalBallDomainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalBallDomainFromEventFlow (rationalBallDomainToEventFlow x) =
        rationalBallDomainFromEventFlow (rationalBallDomainToEventFlow y) :=
    congrArg rationalBallDomainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalBallDomainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalBallDomainTasteGate_single_carrier_alignment_round_trip y)))

instance rationalBallDomainBHistCarrier : BHistCarrier RationalBallDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalBallDomainToEventFlow
  fromEventFlow := rationalBallDomainFromEventFlow

instance rationalBallDomainChapterTasteGate : ChapterTasteGate RationalBallDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalBallDomainFromEventFlow (rationalBallDomainToEventFlow x) = some x
    exact RationalBallDomainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalBallDomainToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RationalBallDomainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalBallDomainChapterTasteGate

theorem RationalBallDomainTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalBallDomainDecodeBHist (rationalBallDomainEncodeBHist h) = h) ∧
      (∀ x : RationalBallDomainUp,
        rationalBallDomainFromEventFlow (rationalBallDomainToEventFlow x) = some x) ∧
      (∀ x y : RationalBallDomainUp,
        rationalBallDomainToEventFlow x = rationalBallDomainToEventFlow y → x = y) ∧
      rationalBallDomainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · intro x
    exact RationalBallDomainTasteGate_single_carrier_alignment_round_trip x
  constructor
  · intro x y heq
    have hread :
        rationalBallDomainFromEventFlow (rationalBallDomainToEventFlow x) =
          rationalBallDomainFromEventFlow (rationalBallDomainToEventFlow y) :=
      congrArg rationalBallDomainFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (RationalBallDomainTasteGate_single_carrier_alignment_round_trip x).symm
        (Eq.trans hread
          (RationalBallDomainTasteGate_single_carrier_alignment_round_trip y)))
  · rfl

end BEDC.Derived.RationalBallDomainUp

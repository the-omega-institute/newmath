import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyShiftEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyShiftEquivalenceUp : Type where
  | mk (Q k S R D H C P N : BHist) : RegularCauchyShiftEquivalenceUp
  deriving DecidableEq

def regularCauchyShiftEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyShiftEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyShiftEquivalenceEncodeBHist h

def regularCauchyShiftEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyShiftEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyShiftEquivalenceDecodeBHist tail)

private theorem RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyShiftEquivalenceDecodeBHist
          (regularCauchyShiftEquivalenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyShiftEquivalenceFields :
    RegularCauchyShiftEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyShiftEquivalenceUp.mk Q k S R D H C P N => [Q, k, S, R, D, H, C, P, N]

def regularCauchyShiftEquivalenceToEventFlow :
    RegularCauchyShiftEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyShiftEquivalenceUp.mk Q k S R D H C P N =>
      [regularCauchyShiftEquivalenceEncodeBHist Q,
        regularCauchyShiftEquivalenceEncodeBHist k,
        regularCauchyShiftEquivalenceEncodeBHist S,
        regularCauchyShiftEquivalenceEncodeBHist R,
        regularCauchyShiftEquivalenceEncodeBHist D,
        regularCauchyShiftEquivalenceEncodeBHist H,
        regularCauchyShiftEquivalenceEncodeBHist C,
        regularCauchyShiftEquivalenceEncodeBHist P,
        regularCauchyShiftEquivalenceEncodeBHist N]

def regularCauchyShiftEquivalenceFromEventFlow :
    EventFlow → Option RegularCauchyShiftEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: restQ =>
      match restQ with
      | k :: restk =>
          match restk with
          | S :: restS =>
              match restS with
              | R :: restR =>
                  match restR with
                  | D :: restD =>
                      match restD with
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
                                            (RegularCauchyShiftEquivalenceUp.mk
                                              (regularCauchyShiftEquivalenceDecodeBHist Q)
                                              (regularCauchyShiftEquivalenceDecodeBHist k)
                                              (regularCauchyShiftEquivalenceDecodeBHist S)
                                              (regularCauchyShiftEquivalenceDecodeBHist R)
                                              (regularCauchyShiftEquivalenceDecodeBHist D)
                                              (regularCauchyShiftEquivalenceDecodeBHist H)
                                              (regularCauchyShiftEquivalenceDecodeBHist C)
                                              (regularCauchyShiftEquivalenceDecodeBHist P)
                                              (regularCauchyShiftEquivalenceDecodeBHist N))
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

private theorem regularCauchyShiftEquivalence_mk_congr
    {Q Q' k k' S S' R R' D D' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q) (hk : k' = k) (hS : S' = S) (hR : R' = R)
    (hD : D' = D) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    RegularCauchyShiftEquivalenceUp.mk Q' k' S' R' D' H' C' P' N' =
      RegularCauchyShiftEquivalenceUp.mk Q k S R D H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hk
  cases hS
  cases hR
  cases hD
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyShiftEquivalenceUp,
      regularCauchyShiftEquivalenceFromEventFlow
          (regularCauchyShiftEquivalenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q k S R D H C P N =>
      exact congrArg some
        (regularCauchyShiftEquivalence_mk_congr
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode Q)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode k)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode S)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode R)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode D)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode H)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode C)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode P)
          (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode N))

private theorem regularCauchyShiftEquivalenceToEventFlow_injective
    {x y : RegularCauchyShiftEquivalenceUp} :
    regularCauchyShiftEquivalenceToEventFlow x =
        regularCauchyShiftEquivalenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyShiftEquivalenceFromEventFlow
          (regularCauchyShiftEquivalenceToEventFlow x) =
        regularCauchyShiftEquivalenceFromEventFlow
          (regularCauchyShiftEquivalenceToEventFlow y) :=
    congrArg regularCauchyShiftEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyShiftEquivalenceBHistCarrier :
    BHistCarrier RegularCauchyShiftEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyShiftEquivalenceToEventFlow
  fromEventFlow := regularCauchyShiftEquivalenceFromEventFlow

instance regularCauchyShiftEquivalenceChapterTasteGate :
    ChapterTasteGate RegularCauchyShiftEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyShiftEquivalenceFromEventFlow
          (regularCauchyShiftEquivalenceToEventFlow x) =
        some x
    exact RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyShiftEquivalenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyShiftEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyShiftEquivalenceChapterTasteGate

theorem RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyShiftEquivalenceDecodeBHist (regularCauchyShiftEquivalenceEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyShiftEquivalenceUp,
        regularCauchyShiftEquivalenceFromEventFlow
            (regularCauchyShiftEquivalenceToEventFlow x) =
          some x) ∧
      (∀ (x : RegularCauchyShiftEquivalenceUp) w m,
        List.Mem w (regularCauchyShiftEquivalenceToEventFlow x) →
          List.Mem m w →
          m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_decode
  constructor
  · exact RegularCauchyShiftEquivalenceTasteGate_single_carrier_alignment_round_trip
  · intro x w m hw hm
    cases m with
    | b0 => exact Or.inl rfl
    | b1 => exact Or.inr rfl

end BEDC.Derived.RegularCauchyShiftEquivalenceUp

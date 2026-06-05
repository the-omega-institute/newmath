import BEDC.Derived.RegularCauchyInterleavingStabilityUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

private theorem regularCauchyInterleavingStabilityTasteGate_decode_encode :
    ∀ h : BHist,
      regularCauchyInterleavingStabilityDecodeBHist
          (regularCauchyInterleavingStabilityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem regularCauchyInterleavingStabilityTasteGate_round_trip :
    ∀ x : RegularCauchyInterleavingStabilityUp,
      regularCauchyInterleavingStabilityFromEventFlow
          (regularCauchyInterleavingStabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B SA SB sigma M W E H C P N =>
      change
        some
          (RegularCauchyInterleavingStabilityUp.mk
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist A))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist B))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist SA))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist SB))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist sigma))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist M))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist W))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist E))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist H))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist C))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist P))
            (regularCauchyInterleavingStabilityDecodeBHist
              (regularCauchyInterleavingStabilityEncodeBHist N))) =
          some (RegularCauchyInterleavingStabilityUp.mk A B SA SB sigma M W E H C P N)
      rw [regularCauchyInterleavingStabilityTasteGate_decode_encode A,
        regularCauchyInterleavingStabilityTasteGate_decode_encode B,
        regularCauchyInterleavingStabilityTasteGate_decode_encode SA,
        regularCauchyInterleavingStabilityTasteGate_decode_encode SB,
        regularCauchyInterleavingStabilityTasteGate_decode_encode sigma,
        regularCauchyInterleavingStabilityTasteGate_decode_encode M,
        regularCauchyInterleavingStabilityTasteGate_decode_encode W,
        regularCauchyInterleavingStabilityTasteGate_decode_encode E,
        regularCauchyInterleavingStabilityTasteGate_decode_encode H,
        regularCauchyInterleavingStabilityTasteGate_decode_encode C,
        regularCauchyInterleavingStabilityTasteGate_decode_encode P,
        regularCauchyInterleavingStabilityTasteGate_decode_encode N]

theorem RegularCauchyInterleavingStabilityUp.RegularCauchyInterleavingStabilityTasteGate_single_carrier_alignment
    [AskSetup] [PackageSetup] {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∀ h : BHist,
        regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchyInterleavingStabilityUp,
        regularCauchyInterleavingStabilityFromEventFlow
            (regularCauchyInterleavingStabilityToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyInterleavingStabilityUp,
          regularCauchyInterleavingStabilityToEventFlow x =
              regularCauchyInterleavingStabilityToEventFlow y →
            x = y) ∧
          (∀ A B SA SB sigma M W E H C P N : BHist,
            RegularCauchyInterleavingStabilityCarrier A B SA SB sigma M W E H C P N
                bundle pkg →
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory SA ∧ UnaryHistory SB ∧
                UnaryHistory sigma ∧ UnaryHistory M ∧ UnaryHistory W ∧
                  UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                    UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg) := by
  -- BEDC touchpoint anchor: BHist BMark RegularCauchyInterleavingStabilityCarrier
  constructor
  · exact regularCauchyInterleavingStabilityTasteGate_decode_encode
  · constructor
    · exact regularCauchyInterleavingStabilityTasteGate_round_trip
    · constructor
      · intro x y flowEq
        have decodedEq :
            regularCauchyInterleavingStabilityFromEventFlow
                (regularCauchyInterleavingStabilityToEventFlow x) =
              regularCauchyInterleavingStabilityFromEventFlow
                (regularCauchyInterleavingStabilityToEventFlow y) :=
          congrArg regularCauchyInterleavingStabilityFromEventFlow flowEq
        exact
          Option.some.inj
            (Eq.trans (regularCauchyInterleavingStabilityTasteGate_round_trip x).symm
              (Eq.trans decodedEq
                (regularCauchyInterleavingStabilityTasteGate_round_trip y)))
      · intro A B SA SB sigma M W E H C P N carrier
        exact carrier

end BEDC.Derived

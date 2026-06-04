import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow

inductive RegularCauchyInterleavingStabilityUp : Type where
  | mk
      (leftSource rightSource leftSchedule rightSchedule selector sharedModulus
        selectedWindows realSeal transport replay provenance name : BHist) :
      RegularCauchyInterleavingStabilityUp
  deriving DecidableEq

def regularCauchyInterleavingStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyInterleavingStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyInterleavingStabilityEncodeBHist h

def regularCauchyInterleavingStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyInterleavingStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyInterleavingStabilityDecodeBHist tail)

private theorem regularCauchyInterleavingStability_decode_encode_bhist :
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

def regularCauchyInterleavingStabilityToEventFlow :
    RegularCauchyInterleavingStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyInterleavingStabilityUp.mk A B SA SB sigma M W E H C P N =>
      [regularCauchyInterleavingStabilityEncodeBHist A,
        regularCauchyInterleavingStabilityEncodeBHist B,
        regularCauchyInterleavingStabilityEncodeBHist SA,
        regularCauchyInterleavingStabilityEncodeBHist SB,
        regularCauchyInterleavingStabilityEncodeBHist sigma,
        regularCauchyInterleavingStabilityEncodeBHist M,
        regularCauchyInterleavingStabilityEncodeBHist W,
        regularCauchyInterleavingStabilityEncodeBHist E,
        regularCauchyInterleavingStabilityEncodeBHist H,
        regularCauchyInterleavingStabilityEncodeBHist C,
        regularCauchyInterleavingStabilityEncodeBHist P,
        regularCauchyInterleavingStabilityEncodeBHist N]

private def regularCauchyInterleavingStabilityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyInterleavingStabilityRawAt index rest

def regularCauchyInterleavingStabilityFromEventFlow :
    EventFlow → Option RegularCauchyInterleavingStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (RegularCauchyInterleavingStabilityUp.mk
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 0 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 1 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 2 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 3 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 4 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 5 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 6 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 7 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 8 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 9 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 10 flow))
          (regularCauchyInterleavingStabilityDecodeBHist
            (regularCauchyInterleavingStabilityRawAt 11 flow)))

private theorem regularCauchyInterleavingStability_round_trip :
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
      rw [regularCauchyInterleavingStability_decode_encode_bhist A,
        regularCauchyInterleavingStability_decode_encode_bhist B,
        regularCauchyInterleavingStability_decode_encode_bhist SA,
        regularCauchyInterleavingStability_decode_encode_bhist SB,
        regularCauchyInterleavingStability_decode_encode_bhist sigma,
        regularCauchyInterleavingStability_decode_encode_bhist M,
        regularCauchyInterleavingStability_decode_encode_bhist W,
        regularCauchyInterleavingStability_decode_encode_bhist E,
        regularCauchyInterleavingStability_decode_encode_bhist H,
        regularCauchyInterleavingStability_decode_encode_bhist C,
        regularCauchyInterleavingStability_decode_encode_bhist P,
        regularCauchyInterleavingStability_decode_encode_bhist N]

theorem RegularCauchyInterleavingStabilityUp.RegularCauchyInterleavingStabilityCarrier_obligations
    [AskSetup] [PackageSetup] (x : RegularCauchyInterleavingStabilityUp) :
    (∀ h : BHist, Cont h BHist.Empty h) ∧
      (Pkg = Pkg) ∧
        ∃ A B SA SB sigma M W E H C P N : BHist,
          x = RegularCauchyInterleavingStabilityUp.mk A B SA SB sigma M W E H C P N ∧
            regularCauchyInterleavingStabilityFromEventFlow
                (regularCauchyInterleavingStabilityToEventFlow x) =
              some x := by
  -- BEDC touchpoint anchor: BHist Cont Pkg
  constructor
  · intro h
    exact cont_intro rfl
  · constructor
    · rfl
    · cases x with
      | mk A B SA SB sigma M W E H C P N =>
          exact
            ⟨A, B, SA, SB, sigma, M, W, E, H, C, P, N, rfl,
              regularCauchyInterleavingStability_round_trip
                (RegularCauchyInterleavingStabilityUp.mk A B SA SB sigma M W E H C P N)⟩

end BEDC.Derived

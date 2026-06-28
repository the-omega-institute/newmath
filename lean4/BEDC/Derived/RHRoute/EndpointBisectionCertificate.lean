import BEDC.Derived.RHRoute.ArgumentPrincipleUp
import BEDC.Derived.RHRoute.CertifiedFirstZero
import BEDC.Derived.Sqrt2BisectionUp

namespace BEDC.Derived.RHRoute.EndpointBisectionCertificate

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.ZetaZeroLocated
open BEDC.Derived.RHRoute.CertifiedFirstZero
open BEDC.Derived.RHRoute.ArgumentPrincipleUp

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ZetaBoxEvaluator.RatComplex

-- 本文件只核验有限端点区间、分支回放和 dyadic 直径账本。
-- Rouche 间隙、Riemann--Siegel 端点模型和 located 极限仍是论文端边界条件。
inductive EndpointBranch where
  | lower : EndpointBranch
  | upper : EndpointBranch

structure EndpointDyadicInterval where
  depth : Nat
  loNum : Nat
  hiNum : Nat
  adjacent : hiNum = loNum + 1

def endpointUnitInterval : EndpointDyadicInterval :=
  { depth := 0
    loNum := 0
    hiNum := 1
    adjacent := rfl }

def endpointLowerChild (I : EndpointDyadicInterval) :
    EndpointDyadicInterval :=
  { depth := Nat.succ I.depth
    loNum := I.loNum + I.loNum
    hiNum := I.loNum + I.loNum + 1
    adjacent := rfl }

def endpointUpperChild (I : EndpointDyadicInterval) :
    EndpointDyadicInterval :=
  { depth := Nat.succ I.depth
    loNum := I.loNum + I.hiNum
    hiNum := I.loNum + I.hiNum + 1
    adjacent := rfl }

def endpointRefine (branch : EndpointBranch)
    (I : EndpointDyadicInterval) : EndpointDyadicInterval :=
  match branch with
  | EndpointBranch.lower => endpointLowerChild I
  | EndpointBranch.upper => endpointUpperChild I

theorem endpointRefine_depth (branch : EndpointBranch)
    (I : EndpointDyadicInterval) :
    (endpointRefine branch I).depth = Nat.succ I.depth := by
  cases branch <;> rfl

theorem endpointRefine_width_num_one (branch : EndpointBranch)
    (I : EndpointDyadicInterval) :
    (endpointRefine branch I).hiNum =
      (endpointRefine branch I).loNum + 1 :=
  (endpointRefine branch I).adjacent

def endpointReplay (seed : EndpointDyadicInterval) :
    List EndpointBranch -> EndpointDyadicInterval
  | [] => seed
  | branch :: rest => endpointReplay (endpointRefine branch seed) rest

theorem endpointReplay_depth
    (seed : EndpointDyadicInterval) (path : List EndpointBranch) :
    (endpointReplay seed path).depth = seed.depth + path.length := by
  induction path generalizing seed with
  | nil =>
      rfl
  | cons branch rest ih =>
      change
        (endpointReplay (endpointRefine branch seed) rest).depth =
          seed.depth + Nat.succ rest.length
      calc
        (endpointReplay (endpointRefine branch seed) rest).depth =
            (endpointRefine branch seed).depth + rest.length := by
              exact ih (endpointRefine branch seed)
        _ = Nat.succ seed.depth + rest.length := by
              rw [endpointRefine_depth]
        _ = Nat.succ (seed.depth + rest.length) := by
              rw [Nat.succ_add]
        _ = seed.depth + Nat.succ rest.length := by
              rw [Nat.add_succ]

theorem endpointReplay_width_num_one
    (seed : EndpointDyadicInterval) (path : List EndpointBranch) :
    (endpointReplay seed path).hiNum =
      (endpointReplay seed path).loNum + 1 :=
  (endpointReplay seed path).adjacent

def endpointReplayByFuel (seed : EndpointDyadicInterval)
    (choose : Nat -> EndpointBranch) : Nat -> EndpointDyadicInterval
  | 0 => seed
  | Nat.succ fuel =>
      endpointRefine (choose fuel) (endpointReplayByFuel seed choose fuel)

theorem endpointReplayByFuel_depth
    (seed : EndpointDyadicInterval) (choose : Nat -> EndpointBranch)
    (fuel : Nat) :
    (endpointReplayByFuel seed choose fuel).depth = seed.depth + fuel := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      change
        (endpointRefine (choose fuel)
          (endpointReplayByFuel seed choose fuel)).depth =
          seed.depth + Nat.succ fuel
      rw [endpointRefine_depth, ih, Nat.add_succ]

def endpointReplayByFuelCell (choose : Nat -> EndpointBranch)
    (fuel : Nat) : EndpointDyadicInterval :=
  endpointReplayByFuel endpointUnitInterval choose fuel

def EndpointDyadicDiameterContract
    (I : EndpointDyadicInterval) (precision : Nat) : Prop :=
  I.depth = precision ∧ I.hiNum = I.loNum + 1

def EndpointDyadicDiameterSchedule
    (cells : Nat -> EndpointDyadicInterval) : Prop :=
  ∀ precision : Nat,
    EndpointDyadicDiameterContract (cells precision) precision

def endpointDiameterDen (precision : Nat) : Nat :=
  BEDC.Derived.Sqrt2BisectionUp.powTwoNat precision

def EndpointDyadicDiameterCofinal
    (cells : Nat -> EndpointDyadicInterval) : Prop :=
  ∀ threshold : Nat, ∃ precision : Nat,
    threshold ≤ endpointDiameterDen precision ∧
      EndpointDyadicDiameterContract (cells precision) precision

theorem endpointDiameterDen_self_covers (threshold : Nat) :
    threshold ≤ endpointDiameterDen threshold := by
  unfold endpointDiameterDen
  induction threshold with
  | zero =>
      exact Nat.zero_le _
  | succ threshold ih =>
      change Nat.succ threshold ≤
        2 * BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold
      have stepToPow :
          Nat.succ threshold ≤
            Nat.succ (BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold) :=
        Nat.succ_le_succ ih
      have powStep :
          Nat.succ (BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold) ≤
            2 * BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold := by
        rw [Nat.two_mul]
        change BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold + 1 ≤
          BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold +
            BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold
        exact Nat.add_le_add_left
          (BEDC.Derived.Sqrt2BisectionUp.powTwoNat_pos threshold)
          (BEDC.Derived.Sqrt2BisectionUp.powTwoNat threshold)
      exact Nat.le_trans stepToPow powStep

theorem endpointReplayByFuelCell_depth
    (choose : Nat -> EndpointBranch) (fuel : Nat) :
    (endpointReplayByFuelCell choose fuel).depth = fuel := by
  unfold endpointReplayByFuelCell
  rw [endpointReplayByFuel_depth]
  exact Nat.zero_add fuel

theorem endpointReplayByFuelCell_diameter_contract
    (choose : Nat -> EndpointBranch) (fuel : Nat) :
    EndpointDyadicDiameterContract
      (endpointReplayByFuelCell choose fuel) fuel := by
  constructor
  · exact endpointReplayByFuelCell_depth choose fuel
  · exact (endpointReplayByFuelCell choose fuel).adjacent

theorem endpointReplayByFuelCell_diameter_schedule
    (choose : Nat -> EndpointBranch) :
    EndpointDyadicDiameterSchedule
      (endpointReplayByFuelCell choose) := by
  intro precision
  exact endpointReplayByFuelCell_diameter_contract choose precision

theorem endpointReplayByFuelCell_diameter_cofinal
    (choose : Nat -> EndpointBranch) :
    EndpointDyadicDiameterCofinal
      (endpointReplayByFuelCell choose) := by
  intro threshold
  exact Exists.intro threshold
    (And.intro (endpointDiameterDen_self_covers threshold)
      (endpointReplayByFuelCell_diameter_contract choose threshold))

def endpointLoRat (I : EndpointDyadicInterval) : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo I.loNum I.depth

def endpointHiRat (I : EndpointDyadicInterval) : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo I.hiNum I.depth

def endpointQInterval (I : EndpointDyadicInterval) : QInterval :=
  { lo := endpointLoRat I
    hi := endpointHiRat I
    valid :=
      BEDC.Derived.Sqrt2BisectionUp.ratLe_natOverPowTwo_of_le
        (k := I.depth)
        (by
          rw [I.adjacent]
          exact Nat.le_succ I.loNum) }

def endpointZeroInterval : QInterval :=
  { lo := ratZero
    hi := ratZero
    valid := ratLe_refl ratZero }

def endpointRealAxisBox (I : EndpointDyadicInterval) : ComplexBox :=
  { re := endpointQInterval I
    im := endpointZeroInterval }

inductive EndpointBisectionProof
    (P : EndpointDyadicInterval -> Prop) :
    EndpointDyadicInterval -> EndpointDyadicInterval -> Type where
  | halt {I : EndpointDyadicInterval} :
      EndpointBisectionProof P I I
  | step {I J : EndpointDyadicInterval} :
      (branch : EndpointBranch) ->
        (preserve : P I -> P (endpointRefine branch I)) ->
          EndpointBisectionProof P (endpointRefine branch I) J ->
            EndpointBisectionProof P I J

namespace EndpointBisectionProof

def branches {P : EndpointDyadicInterval -> Prop}
    {seed final : EndpointDyadicInterval}
    (cert : EndpointBisectionProof P seed final) :
    List EndpointBranch :=
  match cert with
  | EndpointBisectionProof.halt => []
  | EndpointBisectionProof.step branch _ tail =>
      branch :: branches tail

def finalInvariant {P : EndpointDyadicInterval -> Prop}
    {seed final : EndpointDyadicInterval}
    (cert : EndpointBisectionProof P seed final) :
    P seed -> P final :=
  match cert with
  | EndpointBisectionProof.halt => fun seedOk => seedOk
  | EndpointBisectionProof.step _ preserve tail =>
      fun seedOk => finalInvariant tail (preserve seedOk)

theorem verifies {P : EndpointDyadicInterval -> Prop}
    {seed final : EndpointDyadicInterval}
    (cert : EndpointBisectionProof P seed final) :
    endpointReplay seed cert.branches = final := by
  induction cert with
  | halt =>
      rfl
  | step branch _ tail ih =>
      change endpointReplay (endpointRefine branch _) tail.branches = _
      exact ih

theorem final_depth {P : EndpointDyadicInterval -> Prop}
    {seed final : EndpointDyadicInterval}
    (cert : EndpointBisectionProof P seed final) :
    final.depth = seed.depth + cert.branches.length := by
  have replayDepth := endpointReplay_depth seed cert.branches
  have replayEq := congrArg EndpointDyadicInterval.depth (verifies cert)
  exact replayEq.symm.trans replayDepth

theorem final_width_num_one {P : EndpointDyadicInterval -> Prop}
    {seed final : EndpointDyadicInterval}
    (cert : EndpointBisectionProof P seed final) :
    final.hiNum = final.loNum + 1 := by
  have replayWidth := endpointReplay_width_num_one seed cert.branches
  have replayEq := verifies cert
  rw [replayEq] at replayWidth
  exact replayWidth

end EndpointBisectionProof

def sqrt2EndpointInterval
    (I : BEDC.Derived.Sqrt2BisectionUp.Sqrt2BisectInterval) :
    EndpointDyadicInterval :=
  { depth := I.depth
    loNum := I.loNum
    hiNum := I.hiNum
    adjacent := I.adjacent }

theorem sqrt2EndpointInterval_depth_width_bracket (precision : Nat) :
    (sqrt2EndpointInterval
        (BEDC.Derived.Sqrt2BisectionUp.sqrt2BisectRaw precision)).depth =
        precision ∧
      (sqrt2EndpointInterval
        (BEDC.Derived.Sqrt2BisectionUp.sqrt2BisectRaw precision)).hiNum =
        (sqrt2EndpointInterval
          (BEDC.Derived.Sqrt2BisectionUp.sqrt2BisectRaw precision)).loNum +
          1 ∧
        BEDC.Derived.Sqrt2BisectionUp.Sqrt2NatBracket
          (BEDC.Derived.Sqrt2BisectionUp.sqrt2BisectRaw precision) := by
  constructor
  · exact BEDC.Derived.Sqrt2BisectionUp.sqrt2BisectRaw_depth precision
  · constructor
    · exact BEDC.Derived.Sqrt2BisectionUp.sqrt2Bisect_width_num_one precision
    · exact
        BEDC.Derived.Sqrt2BisectionUp.sqrt2Bisect_lo_sq_lt_two_lt_hi_sq
          precision

structure FirstZeroEndpointRows
    (cert : CertifiedZeroIsolation) where
  contour_winding : WindingOne cert.contour.turns
  nested_boxes : BoxStreamNested cert.boxes
  dyadic_box_diameters : BoxStreamDiametersShrink cert.boxes
  point_in_search : ComplexInBox cert.point firstZeroSearchBox

def firstZeroEndpointRows
    (cert : CertifiedZeroIsolation) : FirstZeroEndpointRows cert :=
  { contour_winding := cert.contour.winding_one
    nested_boxes := cert.nested
    dyadic_box_diameters := cert.diameter_bound
    point_in_search :=
      CertifiedZeroIsolation.point_in_search_box cert }

theorem firstZeroEndpointRows_diameter_bound
    (cert : CertifiedZeroIsolation) (precision : Nat) :
    BoxDiameterBound (cert.boxes precision) precision :=
  (firstZeroEndpointRows cert).dyadic_box_diameters precision

theorem firstZeroEndpointRows_located
    (cert : CertifiedZeroIsolation) :
    ZetaZeroLocated cert.point :=
  CertifiedZeroIsolation.located cert

structure ArgumentEndpointRows
    (start final : RationalRectangle) where
  chain : BisectionLocationChain start final
  final_contains : ContainsLocatedZetaZero final

def argumentEndpointRows {start final : RationalRectangle}
    (chain : BisectionLocationChain start final) :
    ArgumentEndpointRows start final :=
  { chain := chain
    final_contains :=
      BEDC.Derived.RHRoute.ArgumentPrincipleUp.bisection_chain_locates_zero
        chain }

theorem argumentEndpointRows_contains
    {start final : RationalRectangle}
    (rows : ArgumentEndpointRows start final) :
    ContainsLocatedZetaZero final :=
  rows.final_contains

structure EndpointLocatedLimitBoundary where
  cells : Nat -> EndpointDyadicInterval
  dyadic_schedule : EndpointDyadicDiameterSchedule cells
  dyadic_cofinal : EndpointDyadicDiameterCofinal cells

def endpointFuelBoundary
    (choose : Nat -> EndpointBranch) : EndpointLocatedLimitBoundary :=
  { cells := endpointReplayByFuelCell choose
    dyadic_schedule := endpointReplayByFuelCell_diameter_schedule choose
    dyadic_cofinal := endpointReplayByFuelCell_diameter_cofinal choose }

theorem endpointFuelBoundary_contract
    (choose : Nat -> EndpointBranch) (precision : Nat) :
    EndpointDyadicDiameterContract
      ((endpointFuelBoundary choose).cells precision) precision :=
  (endpointFuelBoundary choose).dyadic_schedule precision

theorem endpointFuelBoundary_diameter_cofinal
    (choose : Nat -> EndpointBranch) :
    EndpointDyadicDiameterCofinal (endpointFuelBoundary choose).cells :=
  (endpointFuelBoundary choose).dyadic_cofinal

end BEDC.Derived.RHRoute.EndpointBisectionCertificate

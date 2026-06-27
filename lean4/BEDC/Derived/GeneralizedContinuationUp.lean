import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.Derived.LocatedReal
import BEDC.Derived.NonCollapseInvariantUp
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.GeneralizedContinuationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.LocatedReal
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

structure ContinuationSeed where
  domain : BHist
  value : BHist

structure ContinuationSchedule where
  tail : Nat → BHist

def chainDomain (seed : ContinuationSeed) (schedule : ContinuationSchedule) :
    Nat → BHist
  | 0 => seed.domain
  | Nat.succ n => append (chainDomain seed schedule n) (schedule.tail n)

def chainValue (seed : ContinuationSeed) (schedule : ContinuationSchedule) :
    Nat → BHist
  | 0 => seed.value
  | Nat.succ n => append (chainValue seed schedule n) (schedule.tail n)

theorem chainDomain_zero (seed : ContinuationSeed)
    (schedule : ContinuationSchedule) :
    chainDomain seed schedule 0 = seed.domain := by
  rfl

theorem chainValue_zero (seed : ContinuationSeed)
    (schedule : ContinuationSchedule) :
    chainValue seed schedule 0 = seed.value := by
  rfl

theorem chainDomain_step (seed : ContinuationSeed)
    (schedule : ContinuationSchedule) (n : Nat) :
    Cont (chainDomain seed schedule n) (schedule.tail n)
      (chainDomain seed schedule (Nat.succ n)) := by
  rfl

theorem chainValue_step (seed : ContinuationSeed)
    (schedule : ContinuationSchedule) (n : Nat) :
    Cont (chainValue seed schedule n) (schedule.tail n)
      (chainValue seed schedule (Nat.succ n)) := by
  rfl

def tailAtList (fallback : BHist) : List BHist → Nat → BHist
  | [], _ => fallback
  | x :: _xs, 0 => x
  | _x :: xs, Nat.succ n => tailAtList fallback xs n

def finiteSchedule (tails : List BHist) (fallback : BHist) :
    ContinuationSchedule :=
  { tail := fun n => tailAtList fallback tails n }

structure FiniteContinuationData where
  seed : ContinuationSeed
  tails : List BHist
  fallback : BHist

def FiniteContinuationData.schedule (data : FiniteContinuationData) :
    ContinuationSchedule :=
  finiteSchedule data.tails data.fallback

def finiteDomain (data : FiniteContinuationData) (n : Nat) : BHist :=
  chainDomain data.seed data.schedule n

def finiteValue (data : FiniteContinuationData) (n : Nat) : BHist :=
  chainValue data.seed data.schedule n

theorem finiteDomain_step (data : FiniteContinuationData) (n : Nat) :
    Cont (finiteDomain data n) (data.schedule.tail n)
      (finiteDomain data (Nat.succ n)) := by
  exact chainDomain_step data.seed data.schedule n

theorem finiteValue_step (data : FiniteContinuationData) (n : Nat) :
    Cont (finiteValue data n) (data.schedule.tail n)
      (finiteValue data (Nat.succ n)) := by
  exact chainValue_step data.seed data.schedule n

structure GeneralizedContinuationChain where
  seed : ContinuationSeed
  schedule : ContinuationSchedule
  invariant : BHist → BHist → Prop
  initial : invariant seed.domain seed.value
  preserves :
    ∀ n : Nat,
      invariant (chainDomain seed schedule n) (chainValue seed schedule n) →
        invariant (chainDomain seed schedule (Nat.succ n))
          (chainValue seed schedule (Nat.succ n))

theorem GeneralizedContinuationChain.domain_route
    (chain : GeneralizedContinuationChain) (n : Nat) :
    Cont (chainDomain chain.seed chain.schedule n) (chain.schedule.tail n)
      (chainDomain chain.seed chain.schedule (Nat.succ n)) :=
  chainDomain_step chain.seed chain.schedule n

theorem GeneralizedContinuationChain.value_route
    (chain : GeneralizedContinuationChain) (n : Nat) :
    Cont (chainValue chain.seed chain.schedule n) (chain.schedule.tail n)
      (chainValue chain.seed chain.schedule (Nat.succ n)) :=
  chainValue_step chain.seed chain.schedule n

theorem GeneralizedContinuationChain.invariant_at
    (chain : GeneralizedContinuationChain) :
    ∀ n : Nat,
      chain.invariant (chainDomain chain.seed chain.schedule n)
        (chainValue chain.seed chain.schedule n) := by
  intro n
  induction n with
  | zero =>
      exact chain.initial
  | succ n ih =>
      exact chain.preserves n ih

structure LocatedApproximationChain (K : RatMetricKit) where
  data : FiniteContinuationData
  seedPoint : LReal K
  nextPoint : Nat → LReal K → LReal K
  invariant : BHist → LReal K → Prop
  initial : invariant data.seed.domain seedPoint
  preserves :
    ∀ (n : Nat) (point : LReal K),
      invariant (finiteDomain data n) point →
        invariant (finiteDomain data (Nat.succ n)) (nextPoint n point)

def locatedApproxAt {K : RatMetricKit}
    (chain : LocatedApproximationChain K) : Nat → LReal K
  | 0 => chain.seedPoint
  | Nat.succ n => chain.nextPoint n (locatedApproxAt chain n)

theorem locatedApproximationChain_domain_route {K : RatMetricKit}
    (chain : LocatedApproximationChain K) (n : Nat) :
    Cont (finiteDomain chain.data n) (chain.data.schedule.tail n)
      (finiteDomain chain.data (Nat.succ n)) :=
  finiteDomain_step chain.data n

theorem locatedApproximationChain_invariant {K : RatMetricKit}
    (chain : LocatedApproximationChain K) :
    ∀ n : Nat, chain.invariant (finiteDomain chain.data n)
      (locatedApproxAt chain n) := by
  intro n
  induction n with
  | zero =>
      exact chain.initial
  | succ n ih =>
      exact chain.preserves n (locatedApproxAt chain n) ih

structure LocatedNonCollapseContinuation (K : RatMetricKit) where
  seed : LReal K
  next : Nat → LReal K → LReal K
  seed_noncollapse :
    NonCollapseInvariant (K := K) seed
  preserves_noncollapse :
    ∀ (n : Nat) (point : LReal K),
      NonCollapseInvariant (K := K) point →
        NonCollapseInvariant (K := K) (next n point)

def locatedNonCollapseAt {K : RatMetricKit}
    (chain : LocatedNonCollapseContinuation K) : Nat → LReal K
  | 0 => chain.seed
  | Nat.succ n => chain.next n (locatedNonCollapseAt chain n)

theorem locatedNonCollapseAt_invariant {K : RatMetricKit}
    (chain : LocatedNonCollapseContinuation K) :
    ∀ n : Nat,
      NonCollapseInvariant (K := K) (locatedNonCollapseAt chain n) := by
  intro n
  induction n with
  | zero =>
      exact chain.seed_noncollapse
  | succ n ih =>
      exact chain.preserves_noncollapse n (locatedNonCollapseAt chain n) ih

theorem locatedNonCollapseAt_no_rat_retraction {K : RatMetricKit}
    (sep : SeparatingRatMetricKit K)
    (chain : LocatedNonCollapseContinuation K) (n : Nat) :
    ¬ ∃ q : BEDC.Derived.RationalUp.RatNum,
      LRealEq K (locatedNonCollapseAt chain n) (ratToLReal K q) := by
  exact NonCollapseInvariant_no_rat_retraction sep
    (locatedNonCollapseAt_invariant chain n)

structure BoxNonCollapseContinuation (G : BoxGauge) where
  seed : BoxStream G
  next : Nat → BoxStream G → BoxStream G
  seed_noncollapse :
    BoxStreamNonCollapseInvariant G seed
  preserves_noncollapse :
    ∀ (n : Nat) (point : BoxStream G),
      BoxStreamNonCollapseInvariant G point →
        BoxStreamNonCollapseInvariant G (next n point)

def boxNonCollapseAt {G : BoxGauge}
    (chain : BoxNonCollapseContinuation G) : Nat → BoxStream G
  | 0 => chain.seed
  | Nat.succ n => chain.next n (boxNonCollapseAt chain n)

def boxNonCollapseAt_invariant {G : BoxGauge}
    (chain : BoxNonCollapseContinuation G) :
    ∀ n : Nat, BoxStreamNonCollapseInvariant G (boxNonCollapseAt chain n) := by
  intro n
  induction n with
  | zero =>
      exact chain.seed_noncollapse
  | succ n ih =>
      exact chain.preserves_noncollapse n (boxNonCollapseAt chain n) ih

theorem boxNonCollapseAt_no_rat_retraction {G : BoxGauge}
    (chain : BoxNonCollapseContinuation G) (n : Nat) :
    BoxStreamExactRatRetraction G (boxNonCollapseAt chain n) → False := by
  exact BoxStreamNonCollapseInvariant.no_rat_retraction
    (boxNonCollapseAt_invariant chain n)

def zetaBoxStream {G : BoxGauge} {s : CriticalStripInput}
    (evaluator : ZetaBoxEvaluator G s) : BoxStream G :=
  { box := fun k => zetaBox evaluator k
    modulus := fun k => k
    modulus_mono := by
      intro _i _j hij
      exact hij
    fits_at := by
      intro k n hkn
      exact G.fits_weaken hkn (zetaBox_fits evaluator n) }

theorem zetaBoxStream_boxAt {G : BoxGauge} {s : CriticalStripInput}
    (evaluator : ZetaBoxEvaluator G s) (k : Nat) :
    boxAt (zetaBoxStream evaluator) k = zetaBox evaluator k := by
  rfl

theorem zetaBoxStream_fits {G : BoxGauge} {s : CriticalStripInput}
    (evaluator : ZetaBoxEvaluator G s) (k : Nat) :
    G.fits (boxAt (zetaBoxStream evaluator) k) k := by
  exact boxAt_fits (zetaBoxStream evaluator) k

structure ZetaBoxContinuationChain {G : BoxGauge} {s : CriticalStripInput}
    (evaluator : ZetaBoxEvaluator G s) where
  data : FiniteContinuationData
  invariant : BHist → ComplexBox → Prop
  initial : invariant data.seed.domain (zetaBox evaluator 0)
  preserves :
    ∀ n : Nat,
      invariant (finiteDomain data n) (zetaBox evaluator n) →
        invariant (finiteDomain data (Nat.succ n)) (zetaBox evaluator (Nat.succ n))

theorem ZetaBoxContinuationChain.domain_route {G : BoxGauge}
    {s : CriticalStripInput} {evaluator : ZetaBoxEvaluator G s}
    (chain : ZetaBoxContinuationChain evaluator) (n : Nat) :
    Cont (finiteDomain chain.data n) (chain.data.schedule.tail n)
      (finiteDomain chain.data (Nat.succ n)) :=
  finiteDomain_step chain.data n

theorem ZetaBoxContinuationChain.invariant_at {G : BoxGauge}
    {s : CriticalStripInput} {evaluator : ZetaBoxEvaluator G s}
    (chain : ZetaBoxContinuationChain evaluator) :
    ∀ n : Nat, chain.invariant (finiteDomain chain.data n)
      (zetaBox evaluator n) := by
  intro n
  induction n with
  | zero =>
      exact chain.initial
  | succ n ih =>
      exact chain.preserves n ih

theorem ZetaBoxContinuationChain.zeta_fits {G : BoxGauge}
    {s : CriticalStripInput} {evaluator : ZetaBoxEvaluator G s}
    (_chain : ZetaBoxContinuationChain evaluator) (n : Nat) :
    G.fits (zetaBox evaluator n) n :=
  zetaBox_fits evaluator n

end BEDC.Derived.GeneralizedContinuationUp

import BEDC.Derived.PrimeSieveOddExactnessUp
import BEDC.Derived.RHRoute.PrimeSkewDefect
import BEDC.Derived.RHRoute.ZetaSolenoidBound

namespace BEDC.Derived.RHRoute.PrimeCountSolenoidBound

open BEDC.Derived.RHRoute.FinitePrimeWindow

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev IsPrime := BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime
abbrev PrimeWindowNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindowNormalization
abbrev PrimeLocalChannel :=
  BEDC.Derived.RHRoute.UnitaryBalance.PrimeLocalChannel
abbrev MirrorPrimeChannels :=
  BEDC.Derived.RHRoute.PrimeSkewDefect.MirrorPrimeChannels
abbrev PrimeSkewCertificate :=
  BEDC.Derived.RHRoute.PrimeSkewDefect.PrimeSkewCertificate
abbrev BoxGauge := BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge
abbrev CriticalStripInput :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput
abbrev ZetaBoxEvaluator :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaBoxEvaluator
abbrev ZetaSolenoidObject {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) :=
  BEDC.Derived.RHRoute.ZetaSolenoidBound.ZetaSolenoidObject E

/--
范围: 本模块只验证有限素窗口计数和递归数值界检查。这里不声明素数定理、
黎曼猜想、解析延拓、渐近素密度或无限 solenoid 测度定理。
-/
def finitePrimeCount (W : PrimeWindow) : Nat :=
  W.elems.length

theorem finitePrimeCount_eq_length (W : PrimeWindow) :
    finitePrimeCount W = W.elems.length := by
  rfl

theorem finitePrimeCount_member_prime (W : PrimeWindow) {p : Nat} :
    W.mem p -> IsPrime p := by
  intro member
  exact All.mem W.all_prime member

def natLeBool : Nat -> Nat -> Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natLeBool a b

theorem natLeBool_true_le :
    ∀ {a b : Nat}, natLeBool a b = true -> a <= b
  | 0, _b, _checked => Nat.zero_le _b
  | Nat.succ _a, 0, checked => by
      cases checked
  | Nat.succ a, Nat.succ b, checked => by
      exact Nat.succ_le_succ (natLeBool_true_le checked)

theorem natLeBool_self_true :
    ∀ n : Nat, natLeBool n n = true
  | 0 => rfl
  | Nat.succ n => natLeBool_self_true n

structure ComputedPrimeCountBound (W : PrimeWindow) where
  bound : Nat
  checked : natLeBool (finitePrimeCount W) bound = true

namespace ComputedPrimeCountBound

theorem sound {W : PrimeWindow} (B : ComputedPrimeCountBound W) :
    finitePrimeCount W <= B.bound := by
  exact natLeBool_true_le B.checked

end ComputedPrimeCountBound

def exactPrimeCountBound (W : PrimeWindow) : ComputedPrimeCountBound W where
  bound := finitePrimeCount W
  checked := natLeBool_self_true (finitePrimeCount W)

theorem exactPrimeCountBound_sound (W : PrimeWindow) :
    finitePrimeCount W <= (exactPrimeCountBound W).bound := by
  exact (exactPrimeCountBound W).sound

structure FinitePrimeCountSolenoidWindow where
  window : PrimeWindow
  normalization : PrimeWindowNormalization
  normalization_window_eq :
    normalization.sourceWindow.elems = window.elems
  countBound : ComputedPrimeCountBound window

def solenoidWindowPrimeCount
    (S : FinitePrimeCountSolenoidWindow) : Nat :=
  finitePrimeCount S.window

def solenoidWindowPrimeCountBound
    (S : FinitePrimeCountSolenoidWindow) : Nat :=
  S.countBound.bound

theorem finitePrimeCountSolenoid_count_le_bound
    (S : FinitePrimeCountSolenoidWindow) :
    solenoidWindowPrimeCount S <= solenoidWindowPrimeCountBound S := by
  exact S.countBound.sound

theorem finitePrimeCountSolenoid_member_prime
    (S : FinitePrimeCountSolenoidWindow) {p : Nat} :
    S.window.mem p -> IsPrime p := by
  intro member
  exact finitePrimeCount_member_prime S.window member

theorem finitePrimeCountSolenoid_unit_norm
    (S : FinitePrimeCountSolenoidWindow) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        S.normalization.normalizedChannel)
      BEDC.Derived.RationalUp.ratOne := by
  exact S.normalization.unit_norm_transfers

theorem finitePrimeCountSolenoid_den_pos_on_window
    (S : FinitePrimeCountSolenoidWindow) (p : Nat) :
    S.window.mem p -> 0 < S.normalization.normalizedChannel.amp_den p := by
  intro member
  exact S.normalization.den_pos_on_source_window p (by
    unfold PrimeWindow.mem at *
    rw [S.normalization_window_eq]
    exact member)

theorem finitePrimeCountSolenoid_supported_off_window
    (S : FinitePrimeCountSolenoidWindow) (p : Nat) :
    Not (S.window.mem p) ->
      S.normalization.normalizedChannel.amp_num p = 0 := by
  intro outside
  exact S.normalization.supported_off_source_window p (by
    intro sourceMember
    have windowMember : S.window.mem p := by
      unfold PrimeWindow.mem at *
      rw [← S.normalization_window_eq]
      exact sourceMember
    exact outside windowMember)

def zetaSolenoidPrimeCount {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) : Nat :=
  finitePrimeCount object.normalization.sourceWindow

def zetaSolenoidPrimeCountBound {G : BoxGauge} {s : CriticalStripInput}
    {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) :
    ComputedPrimeCountBound object.normalization.sourceWindow :=
  exactPrimeCountBound object.normalization.sourceWindow

theorem zetaSolenoidPrimeCount_bound_sound {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) :
    zetaSolenoidPrimeCount object <=
      (zetaSolenoidPrimeCountBound object).bound := by
  exact (zetaSolenoidPrimeCountBound object).sound

theorem zetaSolenoidPrimeCount_unit_norm {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        object.normalization.normalizedChannel)
      BEDC.Derived.RationalUp.ratOne := by
  exact object.normalization.unit_norm_transfers

theorem zetaSolenoidPrimeCount_member_prime {G : BoxGauge}
    {s : CriticalStripInput} {E : ZetaBoxEvaluator G s}
    (object : ZetaSolenoidObject E) {p : Nat} :
    object.normalization.sourceWindow.mem p -> IsPrime p := by
  intro member
  exact finitePrimeCount_member_prime object.normalization.sourceWindow member

structure OddSievePrimeWindowReadout where
  limit : Nat
  window : PrimeWindow
  sieve_elems :
    window.elems =
      BEDC.Derived.PrimeSieveOddExactnessUp.oddPrimeSieve limit

theorem oddSieveReadout_count_eq_sieve_length
    (readout : OddSievePrimeWindowReadout) :
    finitePrimeCount readout.window =
      (BEDC.Derived.PrimeSieveOddExactnessUp.oddPrimeSieve
        readout.limit).length := by
  unfold finitePrimeCount
  rw [readout.sieve_elems]

def oddSieveReadoutBound
    (readout : OddSievePrimeWindowReadout) :
    ComputedPrimeCountBound readout.window :=
  exactPrimeCountBound readout.window

theorem oddSieveReadout_bound_sound
    (readout : OddSievePrimeWindowReadout) :
    finitePrimeCount readout.window <=
      (oddSieveReadoutBound readout).bound := by
  exact (oddSieveReadoutBound readout).sound

def oddSieveSixteenNodup : NoDup [3, 5, 7, 11, 13] :=
  NoDup.cons (not_mem_of_listMemNat_false rfl)
    (NoDup.cons (not_mem_of_listMemNat_false rfl)
      (NoDup.cons (not_mem_of_listMemNat_false rfl)
        (NoDup.cons (not_mem_of_listMemNat_false rfl)
          (NoDup.cons (not_mem_of_listMemNat_false rfl) NoDup.nil))))

def oddSieveSixteenAllPrime : All IsPrime [3, 5, 7, 11, 13] :=
  All.cons BEDC.Derived.PrimeSieveOddExactnessUp.NatThree_prime
    (All.cons BEDC.Derived.PrimeSieveOddExactnessUp.NatFive_prime
      (All.cons BEDC.Derived.PrimeSieveOddExactnessUp.NatSeven_prime
        (All.cons BEDC.Derived.PrimeSieveOddExactnessUp.NatEleven_prime
          (All.cons
            BEDC.Derived.PrimeSieveOddExactnessUp.NatThirteen_prime
            All.nil))))

def oddSieveSixteenWindow : PrimeWindow where
  elems := [3, 5, 7, 11, 13]
  nodup := oddSieveSixteenNodup
  all_prime := oddSieveSixteenAllPrime

def oddSieveSixteenReadout : OddSievePrimeWindowReadout where
  limit := 16
  window := oddSieveSixteenWindow
  sieve_elems :=
    BEDC.Derived.PrimeSieveOddExactnessUp.oddPrimeSieve_sixteen_exact.symm

theorem oddSieveSixteen_count_eq_five :
    finitePrimeCount oddSieveSixteenWindow = 5 := by
  rfl

theorem oddSieveSixteen_sieve_count_eq_five :
    (BEDC.Derived.PrimeSieveOddExactnessUp.oddPrimeSieve 16).length = 5 := by
  rw [BEDC.Derived.PrimeSieveOddExactnessUp.oddPrimeSieve_sixteen_exact]
  rfl

theorem oddSieveSixteen_bound_checked :
    natLeBool (finitePrimeCount oddSieveSixteenWindow) 5 = true := by
  rfl

def oddSieveSixteenComputedBound :
    ComputedPrimeCountBound oddSieveSixteenWindow where
  bound := 5
  checked := oddSieveSixteen_bound_checked

theorem oddSieveSixteen_count_le_five :
    finitePrimeCount oddSieveSixteenWindow <= 5 := by
  exact oddSieveSixteenComputedBound.sound

theorem oddSieveSixteen_all_members_prime {p : Nat} :
    oddSieveSixteenWindow.mem p -> IsPrime p := by
  intro member
  exact finitePrimeCount_member_prime oddSieveSixteenWindow member

theorem oddSieveSixteen_survivor_readback :
    (BEDC.Derived.PrimeSieveOddExactnessUp.oddSieveSurvivesBool 16 3 =
        true ∧ IsPrime 3) ∧
      (BEDC.Derived.PrimeSieveOddExactnessUp.oddSieveSurvivesBool 16 5 =
          true ∧ IsPrime 5) ∧
        (BEDC.Derived.PrimeSieveOddExactnessUp.oddSieveSurvivesBool 16 7 =
            true ∧ IsPrime 7) ∧
          (BEDC.Derived.PrimeSieveOddExactnessUp.oddSieveSurvivesBool 16 11 =
              true ∧ IsPrime 11) ∧
            (BEDC.Derived.PrimeSieveOddExactnessUp.oddSieveSurvivesBool 16 13 =
                true ∧ IsPrime 13) ∧
              BEDC.Derived.PrimeSieveOddExactnessUp.oddSieveSurvivesBool
                  16 9 = false ∧
                BEDC.Derived.PrimeSieveOddExactnessUp.oddSieveSurvivesBool
                  16 15 = false := by
  exact BEDC.Derived.PrimeSieveOddExactnessUp.smallRangeOddSieveExactness

structure OddSievePrimeCountSolenoidWindow where
  readout : OddSievePrimeWindowReadout
  solenoid : FinitePrimeCountSolenoidWindow
  same_window : solenoid.window.elems = readout.window.elems

theorem oddSieveSolenoid_count_eq_sieve_length
    (S : OddSievePrimeCountSolenoidWindow) :
    solenoidWindowPrimeCount S.solenoid =
      (BEDC.Derived.PrimeSieveOddExactnessUp.oddPrimeSieve
        S.readout.limit).length := by
  unfold solenoidWindowPrimeCount finitePrimeCount
  exact congrArg List.length (Eq.trans S.same_window S.readout.sieve_elems)

theorem oddSieveSolenoid_count_le_bound
    (S : OddSievePrimeCountSolenoidWindow) :
    solenoidWindowPrimeCount S.solenoid <=
      solenoidWindowPrimeCountBound S.solenoid := by
  exact finitePrimeCountSolenoid_count_le_bound S.solenoid

structure PrimeSkewCountWindowReadout where
  surface : FinitePrimeCountSolenoidWindow
  channels : MirrorPrimeChannels
  source_window_eq : channels.source.window.elems = surface.window.elems
  certificate : PrimeSkewCertificate channels

theorem primeSkewCountWindow_selected_in_window
    (R : PrimeSkewCountWindowReadout) :
    R.surface.window.mem R.certificate.prime := by
  unfold PrimeWindow.mem at *
  rw [← R.source_window_eq]
  exact R.certificate.source_mem

theorem primeSkewCountWindow_selected_is_prime
    (R : PrimeSkewCountWindowReadout) :
    IsPrime R.certificate.prime := by
  exact finitePrimeCountSolenoid_member_prime R.surface
    (primeSkewCountWindow_selected_in_window R)

theorem primeSkewCountWindow_source_raw_apart
    (R : PrimeSkewCountWindowReadout) :
    R.channels.source.amp_num R.certificate.prime ≠
      Int.ofNat (R.channels.source.amp_den R.certificate.prime) := by
  exact R.certificate.source_deviation_raw_apart

theorem primeSkewCountWindow_count_le_bound
    (R : PrimeSkewCountWindowReadout) :
    solenoidWindowPrimeCount R.surface <=
      solenoidWindowPrimeCountBound R.surface := by
  exact finitePrimeCountSolenoid_count_le_bound R.surface

end BEDC.Derived.RHRoute.PrimeCountSolenoidBound

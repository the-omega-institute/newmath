import BEDC.Derived.PadicUp.Multiplicative
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.GcdUp
import BEDC.Derived.LatticeUp.NatExtrema
import BEDC.Derived.KummerTheoremUp

namespace BEDC.Derived.PadicValuationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.GcdUp
open BEDC.Derived.LatticeUp
open BEDC.Derived.PreorderUp

def padicValuationNat (p n k : BHist) : Prop :=
  IsPadicValNat p n k

def padicPrimePowerDividesNat (p k n : BHist) : Prop :=
  PDvdNat p k n

theorem padicValuationNat_divides {p n k : BHist} :
    padicValuationNat p n k -> padicPrimePowerDividesNat p k n := by
  intro valuation
  exact valuation.left

theorem padicValuationNat_not_succ {p n k : BHist} :
    padicValuationNat p n k ->
      padicPrimePowerDividesNat p (BHist.e1 k) n -> False := by
  intro valuation
  exact valuation.right

theorem padicValuationNat_unique {p n k l : BHist} :
    padicValuationNat p n k -> padicValuationNat p n l -> hsame k l := by
  intro left right
  exact IsPadicValNat_unique left right

theorem padicValuationNat_zero_of_not_p_dvd {p n : BHist} :
    UnaryHistory p -> UnaryHistory n -> (NatDivides p n -> False) ->
      padicValuationNat p n BHist.Empty := by
  intro pUnary nUnary notDivides
  exact IsPadicValNat_zero_of_not_p_dvd pUnary nUnary notDivides

theorem padicValuationNat_self_prime_one {p : BHist} :
    NatPrime p -> padicValuationNat p p NatOne := by
  intro prime
  exact NatPrime_self_valuation_one prime

theorem padicValuationNat_other_prime_zero {p q : BHist} :
    NatPrime p -> NatPrime q -> (hsame p q -> False) ->
      padicValuationNat p q BHist.Empty := by
  intro pPrime qPrime notSame
  exact NatPrime_other_valuation_zero pPrime qPrime notSame

theorem padicPrimePowerDividesNat_prefix_down {p n lower upper : BHist} :
    padicPrimePowerDividesNat p upper n -> PreorderPrefixLE lower upper ->
      padicPrimePowerDividesNat p lower n := by
  intro divides prefixLE
  cases prefixLE with
  | intro tail data =>
      exact PDvdNat_cont_prefix_down data.left data.right divides

theorem padicPrimePowerDividesNat_divides_trans {p k n m : BHist} :
    padicPrimePowerDividesNat p k n -> NatDivides n m ->
      padicPrimePowerDividesNat p k m := by
  intro dividesPower dividesTarget
  cases dividesPower with
  | intro pk data =>
      exact ⟨pk, data.left, NatDivides_transitive data.right dividesTarget⟩

theorem padicValuationNat_lower_power_divides {p n lower value : BHist} :
    padicValuationNat p n value -> PreorderPrefixLE lower value ->
      padicPrimePowerDividesNat p lower n := by
  intro valuation lowerLeValue
  exact padicPrimePowerDividesNat_prefix_down valuation.left lowerLeValue

theorem padicValuationNat_lower_bound_le_value {p n lower value : BHist} :
    padicValuationNat p n value -> padicPrimePowerDividesNat p lower n ->
      PreorderPrefixLE lower value := by
  intro valuation lowerDivides
  have lowerUnary : UnaryHistory lower := (PDvdNat_power_unary lowerDivides).right
  have valueUnary : UnaryHistory value := (PDvdNat_power_unary valuation.left).right
  have trichotomy := NatUnaryPrefix_trichotomy_hsame_strict lowerUnary valueUnary
  cases trichotomy with
  | inl same =>
      exact PreorderPrefixLE_of_hsame same
  | inr strictCases =>
      cases strictCases with
      | inl lowerStrictValue =>
          cases lowerStrictValue with
          | intro tail data =>
              exact ⟨tail, data.left, data.right.right⟩
      | inr valueStrictLower =>
          cases valueStrictLower with
          | intro tail data =>
              cases data with
              | intro tailUnary rest =>
                  cases rest with
                  | intro tailNonempty tailCont =>
                      cases tail with
                      | Empty =>
                          exact False.elim (tailNonempty rfl)
                      | e0 tailTail =>
                          cases tailUnary
                      | e1 tailTail =>
                          have innerUnary : UnaryHistory tailTail :=
                            unary_e1_inversion tailUnary
                          have succCont : Cont (BHist.e1 value) tailTail lower := by
                            exact cont_intro
                              (tailCont.trans
                                (unary_append_e1_left (h := tailTail) (k := value)
                                  innerUnary).symm)
                          have succDivides :
                              padicPrimePowerDividesNat p (BHist.e1 value) n :=
                            PDvdNat_cont_prefix_down innerUnary succCont lowerDivides
                          exact False.elim (valuation.right succDivides)

theorem padicValuationNat_mul_additive {p j k s x y z : BHist} :
    NatPrime p -> padicValuationNat p x j -> padicValuationNat p y k ->
      NatAdd j k s -> NatMul x y z -> padicValuationNat p z s := by
  intro prime left right add product
  exact IsPadicValNat_mul_add_exact_of_prime prime left right add product

theorem padicValuationNat_natMulFn_additive {p j k s x y : BHist} :
    NatPrime p -> padicValuationNat p x j -> padicValuationNat p y k ->
      NatAdd j k s -> padicValuationNat p (BEDC.Derived.IntUp.natMulFn x y) s := by
  intro prime left right add
  exact padicValuationNat_mul_additive prime left right add
    (BEDC.Derived.IntUp.natMulFn_rel
      (PDvdNat_dividend_unary left.left)
      (PDvdNat_dividend_unary right.left))

theorem padicValuationNat_add_lower_bound {p j k lower x y z : BHist} :
    padicValuationNat p x j -> padicValuationNat p y k ->
      PreorderPrefixLE lower j -> PreorderPrefixLE lower k ->
        NatAdd x y z -> padicPrimePowerDividesNat p lower z := by
  intro left right lowerLeJ lowerLeK add
  have dividesX : padicPrimePowerDividesNat p lower x :=
    padicValuationNat_lower_power_divides left lowerLeJ
  have dividesY : padicPrimePowerDividesNat p lower y :=
    padicValuationNat_lower_power_divides right lowerLeK
  exact PDvdNat_cont_closed dividesX dividesY add.right.right

theorem padicValuationNat_ultrametric_lower {p j k x y z : BHist} :
    padicValuationNat p x j -> padicValuationNat p y k -> NatAdd x y z ->
      padicPrimePowerDividesNat p (natMin j k) z := by
  intro left right add
  have jUnary : UnaryHistory j := (PDvdNat_power_unary left.left).right
  have kUnary : UnaryHistory k := (PDvdNat_power_unary right.left).right
  exact padicValuationNat_add_lower_bound left right
    (natMin_le_left jUnary) (natMin_le_right kUnary) add

theorem padicValuationNat_ultrametric {p j k r x y z : BHist} :
    padicValuationNat p x j -> padicValuationNat p y k ->
      NatAdd x y z -> padicValuationNat p z r ->
        PreorderPrefixLE (natMin j k) r := by
  intro left right add sumVal
  exact padicValuationNat_lower_bound_le_value sumVal
    (padicValuationNat_ultrametric_lower left right add)

theorem padicPrimePowerDividesNat_common_gcd {p k a b g : BHist} :
    padicPrimePowerDividesNat p k a -> padicPrimePowerDividesNat p k b ->
      NatGcd a b g -> padicPrimePowerDividesNat p k g := by
  intro left right gcd
  cases left with
  | intro pk leftData =>
      cases right with
      | intro pkRight rightData =>
          have samePower : hsame pkRight pk :=
            PPow_functional rightData.left leftData.left
          have rightDividesByLeftPower : NatDivides pk b :=
            (NatDivides_divisor_hsame_transport rightData.right samePower).right
          exact ⟨pk, leftData.left,
            NatGcd_greatest gcd leftData.right rightDividesByLeftPower⟩

theorem padicValuationNat_gcd_min {p a b g j k r : BHist} :
    NatGcd a b g -> padicValuationNat p a j -> padicValuationNat p b k ->
      padicValuationNat p g r -> hsame r (natMin j k) := by
  intro gcd valA valB valG
  have rDividesA : padicPrimePowerDividesNat p r a :=
    padicPrimePowerDividesNat_divides_trans valG.left (NatGcd_dvd_left gcd)
  have rDividesB : padicPrimePowerDividesNat p r b :=
    padicPrimePowerDividesNat_divides_trans valG.left (NatGcd_dvd_right gcd)
  have rLeJ : PreorderPrefixLE r j :=
    padicValuationNat_lower_bound_le_value valA rDividesA
  have rLeK : PreorderPrefixLE r k :=
    padicValuationNat_lower_bound_le_value valB rDividesB
  have rUnary : UnaryHistory r := (PDvdNat_power_unary valG.left).right
  have rLeMin : PreorderPrefixLE r (natMin j k) :=
    natMin_greatest_lower_bound rUnary rLeJ rLeK
  have jUnary : UnaryHistory j := (PDvdNat_power_unary valA.left).right
  have kUnary : UnaryHistory k := (PDvdNat_power_unary valB.left).right
  have minDividesA : padicPrimePowerDividesNat p (natMin j k) a :=
    padicValuationNat_lower_power_divides valA (natMin_le_left jUnary)
  have minDividesB : padicPrimePowerDividesNat p (natMin j k) b :=
    padicValuationNat_lower_power_divides valB (natMin_le_right kUnary)
  have minDividesG : padicPrimePowerDividesNat p (natMin j k) g :=
    padicPrimePowerDividesNat_common_gcd minDividesA minDividesB gcd
  have minLeR : PreorderPrefixLE (natMin j k) r :=
    padicValuationNat_lower_bound_le_value valG minDividesG
  exact PreorderPrefixLE_antisymm_hsame rLeMin minLeR

theorem padicValuationNat_lcm_max_lower {p a b l j k r : BHist} :
    NatLcm a b l -> padicValuationNat p a j -> padicValuationNat p b k ->
      padicValuationNat p l r -> PreorderPrefixLE (natMax j k) r := by
  intro lcm valA valB valL
  have jDividesL : padicPrimePowerDividesNat p j l :=
    padicPrimePowerDividesNat_divides_trans valA.left (NatLcm_left_dvd lcm)
  have kDividesL : padicPrimePowerDividesNat p k l :=
    padicPrimePowerDividesNat_divides_trans valB.left (NatLcm_right_dvd lcm)
  have jLeR : PreorderPrefixLE j r :=
    padicValuationNat_lower_bound_le_value valL jDividesL
  have kLeR : PreorderPrefixLE k r :=
    padicValuationNat_lower_bound_le_value valL kDividesL
  have rUnary : UnaryHistory r := (PDvdNat_power_unary valL.left).right
  exact natMax_least_upper_bound rUnary jLeR kLeR

def factorialPadicValuationTrace (p delta n valuation digitSum : Nat) : Prop :=
  BEDC.Derived.KummerTheoremUp.factorialPadicValuation
    p delta n valuation digitSum

def basePDigitSumTrace (p delta n valuation digitSum : Nat) : Prop :=
  BEDC.Derived.KummerTheoremUp.basePDigitSum
    p delta n valuation digitSum

theorem factorialPadicValuationTrace_legendre_floor
    {p delta n valuation digitSum : Nat} :
    factorialPadicValuationTrace p delta n valuation digitSum ->
      delta * valuation + digitSum = n := by
  intro trace
  exact BEDC.Derived.KummerTheoremUp.factorialPadicValuation_legendre_floor trace

theorem factorialPadicValuationTrace_unary
    (p delta n valuation digitSum : Nat) :
    UnaryHistory
      (BEDC.Derived.KummerTheoremUp.factorialPadicValuationUnary
        p delta n valuation digitSum) := by
  exact BEDC.Derived.KummerTheoremUp.factorialPadicValuationUnary_result
    p delta n valuation digitSum

theorem padicValuationNat_prime_factor_count {p n : BHist} {entries : List BHist} :
    PrimeFactorizationProduct entries n -> NatPrime p ->
      padicValuationNat p n (primeCount p entries) := by
  intro product prime
  exact primeCount_is_valuation product prime

theorem padicValuationNat_prime_factor_count_unique
    {p n k : BHist} {entries : List BHist} :
    PrimeFactorizationProduct entries n -> NatPrime p ->
      padicValuationNat p n k -> hsame (primeCount p entries) k := by
  intro product prime valuation
  exact primeCount_eq_valuation product prime valuation

end BEDC.Derived.PadicValuationUp

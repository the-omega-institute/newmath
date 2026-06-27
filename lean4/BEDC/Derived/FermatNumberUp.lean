import BEDC.Derived.GcdUp
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.FermatNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.GcdUp
open BEDC.Derived.PadicUp

abbrev NatOne : BHist := BHist.e1 BHist.Empty
abbrev NatTwo : BHist := BHist.e1 NatOne

def twoPowTowerNat : Nat -> Nat
  | 0 => 2
  | n + 1 => twoPowTowerNat n * twoPowTowerNat n

def fermatNumberNat (n : Nat) : Nat :=
  twoPowTowerNat n + 1

def fermatNumber (n : Nat) : BHist :=
  natToUnary (fermatNumberNat n)

def fermatPrefixProductNat : Nat -> Nat
  | 0 => 1
  | n + 1 => fermatPrefixProductNat n * fermatNumberNat n

def fermatPrefixProduct (n : Nat) : BHist :=
  natToUnary (fermatPrefixProductNat n)

def FermatCongruentTwoMod (modulus value : BHist) : Prop :=
  ∃ q product : BHist, NatMul modulus q product ∧ NatAdd product NatTwo value

private theorem NatOne_unary : UnaryHistory NatOne :=
  unary_e1_closed unary_empty

private theorem NatTwo_unary : UnaryHistory NatTwo :=
  unary_e1_closed NatOne_unary

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem NatDivides_length_factor {d n : BHist} :
    NatDivides d n ->
      ∃ qLen : Nat, bwordLength n = bwordLength d * qLen := by
  intro divides
  cases divides with
  | intro q qData =>
      exact ⟨bwordLength q, NatMul_bwordLength qData.right⟩

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [Nat.left_distrib]
      rw [ih]

private theorem nat_add_shuffle_pure (x y a b : Nat) :
    (x + y) + (a + b) = (x + a) + (y + b) := by
  calc
    (x + y) + (a + b) = x + (y + (a + b)) := by
      rw [Nat.add_assoc]
    _ = x + ((y + a) + b) := by
      rw [<- Nat.add_assoc y a b]
    _ = x + ((a + y) + b) := by
      rw [Nat.add_comm y a]
    _ = x + (a + (y + b)) := by
      rw [Nat.add_assoc a y b]
    _ = (x + a) + (y + b) := by
      rw [<- Nat.add_assoc x a (y + b)]

private theorem nat_right_distrib_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [ih]
      exact nat_add_shuffle_pure (a * c) (b * c) a b

private theorem fermat_square_step_nat (p : Nat) :
    p * ((p + 1) + 1) + 1 = (p + 1) * (p + 1) := by
  rw [nat_right_distrib_pure p 1 (p + 1)]
  rw [Nat.one_mul]
  rw [Nat.mul_succ]
  rw [Nat.add_assoc]

private theorem two_mul_eq_two_mul_add_one_absurd :
    ∀ a b : Nat, 2 * a = 2 * b + 1 -> False
  | 0, _b, h => by cases h
  | Nat.succ a, 0, h => by
      have h' : Nat.succ (Nat.succ (2 * a)) = Nat.succ 0 := h
      have h'' : Nat.succ (2 * a) = 0 := Nat.succ.inj h'
      cases h''
  | Nat.succ a, Nat.succ b, h => by
      have h' : Nat.succ (Nat.succ (2 * a)) =
          Nat.succ (Nat.succ (2 * b + 1)) := h
      exact two_mul_eq_two_mul_add_one_absurd a b
        (Nat.succ.inj (Nat.succ.inj h'))

theorem fermatPrefixProductNat_power (n : Nat) :
    fermatPrefixProductNat n + 1 = twoPowTowerNat n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change fermatPrefixProductNat n * (twoPowTowerNat n + 1) + 1 =
        twoPowTowerNat n * twoPowTowerNat n
      rw [<- ih]
      exact fermat_square_step_nat (fermatPrefixProductNat n)

theorem fermatNumber_product_relation_nat (n : Nat) :
    fermatPrefixProductNat n + 2 = fermatNumberNat n := by
  unfold fermatNumberNat
  rw [<- fermatPrefixProductNat_power n]

theorem twoPowTowerNat_even_witness (n : Nat) :
    ∃ q : Nat, twoPowTowerNat n = 2 * q := by
  induction n with
  | zero =>
      exact ⟨1, rfl⟩
  | succ n ih =>
      cases ih with
      | intro q hq =>
          exact ⟨(2 * q) * q, by
            change twoPowTowerNat n * twoPowTowerNat n = 2 * (2 * q * q)
            rw [hq]
            calc
              (2 * q) * (2 * q) = ((2 * q) * 2) * q := by
                rw [<- nat_mul_assoc_pure (2 * q) 2 q]
              _ = (2 * (2 * q)) * q := by
                rw [Nat.mul_comm (2 * q) 2]
              _ = 2 * ((2 * q) * q) := by
                rw [nat_mul_assoc_pure 2 (2 * q) q]⟩

theorem fermatNumber_unary (n : Nat) :
    UnaryHistory (fermatNumber n) := by
  unfold fermatNumber
  exact natToUnary_unary _

theorem fermatPrefixProduct_unary (n : Nat) :
    UnaryHistory (fermatPrefixProduct n) := by
  unfold fermatPrefixProduct
  exact natToUnary_unary _

theorem fermatNumber_product_relation (n : Nat) :
    NatAdd (fermatPrefixProduct n) NatTwo (fermatNumber n) := by
  constructor
  · exact fermatPrefixProduct_unary n
  · constructor
    · exact NatTwo_unary
    · apply cont_intro
      apply unary_hsame_of_length
      · exact fermatNumber_unary n
      · exact unary_append_closed (fermatPrefixProduct_unary n) NatTwo_unary
      · rw [fermatNumber, fermatPrefixProduct, natToUnary_length]
        unfold NatTwo NatOne
        rw [BEDC.FKernel.ExternalBinary.bwordLength_append]
        rw [natToUnary_length]
        change fermatNumberNat n = fermatPrefixProductNat n + 2
        exact (fermatNumber_product_relation_nat n).symm

theorem fermatNumber_prefix_factor_divides {k n : Nat} :
    k < n -> NatDivides (fermatNumber k) (fermatPrefixProduct n) := by
  intro hlt
  induction n with
  | zero =>
      exact False.elim (Nat.not_lt_zero k hlt)
  | succ n ih =>
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with
      | inl hltPrev =>
          have prevDivides : NatDivides (fermatNumber k) (fermatPrefixProduct n) :=
            ih hltPrev
          have productRel :
              NatMul (fermatPrefixProduct n) (fermatNumber n)
                (fermatPrefixProduct (n + 1)) := by
            unfold fermatPrefixProduct
            exact zpuNatToUnary_NatMul_rel (fermatPrefixProductNat n) (fermatNumberNat n)
          exact NatDivides_mul_right_factor_closed (fermatNumber_unary n) prevDivides productRel
      | inr same =>
          subst k
          have productRel :
              NatMul (fermatPrefixProduct n) (fermatNumber n)
                (fermatPrefixProduct (n + 1)) := by
            unfold fermatPrefixProduct
            exact zpuNatToUnary_NatMul_rel (fermatPrefixProductNat n) (fermatNumberNat n)
          exact NatDivides_mul_right_closed (fermatPrefixProduct_unary n)
            (fermatNumber_unary n) productRel

theorem fermatNumber_congruent_two_mod_factor_of_lt {k n : Nat} :
    k < n -> FermatCongruentTwoMod (fermatNumber k) (fermatNumber n) := by
  intro hlt
  cases fermatNumber_prefix_factor_divides hlt with
  | intro q qData =>
      exact ⟨q, fermatPrefixProduct n, qData.right, fermatNumber_product_relation n⟩

theorem NatTwo_not_divides_fermatNumber (n : Nat) :
    NatDivides NatTwo (fermatNumber n) -> False := by
  intro divides
  cases NatDivides_length_factor divides with
  | intro qLen lengthEq =>
      unfold fermatNumber fermatNumberNat NatTwo NatOne at lengthEq
      rw [natToUnary_length] at lengthEq
      change twoPowTowerNat n + 1 = 2 * qLen at lengthEq
      cases twoPowTowerNat_even_witness n with
      | intro half halfEq =>
          have oddEven : 2 * qLen = 2 * half + 1 := by
            exact lengthEq.symm.trans (congrArg (fun t => t + 1) halfEq)
          exact two_mul_eq_two_mul_add_one_absurd qLen half oddEven

private theorem NatGcd_result_hsame_transport {a b g g' : BHist} :
    NatGcd a b g -> hsame g g' -> NatGcd a b g' := by
  intro gcd sameG
  constructor
  · exact NatGcd_left_unary gcd
  · constructor
    · exact NatGcd_right_unary gcd
    · constructor
      · exact unary_transport (NatGcd_result_unary gcd) sameG
      · constructor
        · exact (NatDivides_divisor_hsame_transport
            (NatGcd_dvd_left gcd) sameG).right
        · constructor
          · exact (NatDivides_divisor_hsame_transport
              (NatGcd_dvd_right gcd) sameG).right
          · intro d dividesA dividesB
            exact (NatDivides_dividend_hsame_transport
              (NatGcd_greatest gcd dividesA dividesB) sameG).right

theorem NatGcd_symm {a b g : BHist} :
    NatGcd a b g -> NatGcd b a g := by
  intro gcd
  constructor
  · exact NatGcd_right_unary gcd
  · constructor
    · exact NatGcd_left_unary gcd
    · constructor
      · exact NatGcd_result_unary gcd
      · constructor
        · exact NatGcd_dvd_right gcd
        · constructor
          · exact NatGcd_dvd_left gcd
          · intro d dividesB dividesA
            exact NatGcd_greatest gcd dividesA dividesB

theorem fermatNumber_gcd_one_of_lt {k n : Nat} :
    k < n -> NatGcd (fermatNumber k) (fermatNumber n) NatOne := by
  intro hlt
  constructor
  · exact fermatNumber_unary k
  · constructor
    · exact fermatNumber_unary n
    · constructor
      · exact NatOne_unary
      · constructor
        · exact (NatDivides_reflexive_pair (fermatNumber_unary k)).left
        · constructor
          · exact (NatDivides_reflexive_pair (fermatNumber_unary n)).left
          · intro d dividesLeft dividesRight
            cases fermatNumber_congruent_two_mod_factor_of_lt hlt with
            | intro q data =>
                cases data with
                | intro product data =>
                    have dNonempty : hsame d BHist.Empty -> False := by
                      intro dEmpty
                      cases dEmpty
                      have fermatEmpty : hsame (fermatNumber k) BHist.Empty :=
                        NatDivides_empty_left_result_empty dividesLeft
                      unfold fermatNumber fermatNumberNat natToUnary at fermatEmpty
                      exact not_hsame_e1_empty fermatEmpty
                    have dDividesProduct : NatDivides d product :=
                      NatDivides_transitive dividesLeft ⟨q, NatMul_right_unary data.left,
                        data.left⟩
                    have dDividesTwo : NatDivides d NatTwo :=
                      dvd_tail_of_dvd_sum (NatDivides_divisor_unary dividesLeft) dNonempty
                        data.right dDividesProduct dividesRight
                    cases NatDivides_nonempty_result_boundary dDividesTwo NatTwo_unary
                        (fun empty => not_hsame_e1_empty empty) with
                    | inl sameDTwo =>
                        have twoDividesLeft : NatDivides NatTwo (fermatNumber k) :=
                          (NatDivides_divisor_hsame_transport dividesLeft sameDTwo).right
                        exact False.elim (NatTwo_not_divides_fermatNumber k twoDividesLeft)
                    | inr strictDTwo =>
                        have dCases :=
                          NatUnaryStrictPrefix_successor_boundary_local
                            (NatDivides_divisor_unary dividesLeft) strictDTwo
                        cases dCases with
                        | inl sameDOne =>
                            exact (NatDivides_divisor_hsame_transport
                              (NatDivides_unit_left_iff.mpr NatOne_unary)
                              (hsame_symm sameDOne)).right
                        | inr strictDOne =>
                            have dLenLtOne :=
                              NatUnaryStrictPrefix_length_lt
                                (NatDivides_divisor_unary dividesLeft) strictDOne
                            have dEmpty : hsame d BHist.Empty := by
                              have lenZero : bwordLength d = 0 := by
                                generalize hlen : bwordLength d = len at dLenLtOne
                                cases len with
                                | zero =>
                                    rfl
                                | succ t =>
                                    have impossible : Nat.succ t ≤ 0 :=
                                      Nat.succ_le_succ_iff.mp dLenLtOne
                                    exact False.elim (Nat.not_succ_le_zero t impossible)
                              apply unary_hsame_of_length
                                (NatDivides_divisor_unary dividesLeft) unary_empty
                              exact lenZero
                            exact False.elim (dNonempty dEmpty)

theorem fermatNumber_pairwise_coprime {m n : Nat} :
    m ≠ n -> NatGcd (fermatNumber m) (fermatNumber n) NatOne := by
  intro hne
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
      exact fermatNumber_gcd_one_of_lt hlt
  | inr hgt =>
      exact NatGcd_symm (fermatNumber_gcd_one_of_lt hgt)

end BEDC.Derived.FermatNumberUp

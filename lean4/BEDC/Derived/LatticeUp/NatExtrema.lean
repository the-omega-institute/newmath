import BEDC.Derived.GcdUp
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp
open BEDC.Derived.PreorderUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.NatUp

private def natMinLen : Nat -> Nat -> Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | a + 1, b + 1 => natMinLen a b + 1

private def natMaxLen : Nat -> Nat -> Nat
  | 0, b => b
  | a + 1, 0 => a + 1
  | a + 1, b + 1 => natMaxLen a b + 1

def natMin (a b : BHist) : BHist :=
  natToUnary (natMinLen (bwordLength a) (bwordLength b))

def natMax (a b : BHist) : BHist :=
  natToUnary (natMaxLen (bwordLength a) (bwordLength b))

def natLcm (a b : BHist) : BHist :=
  natToUnary (Nat.lcm (bwordLength a) (bwordLength b))

private theorem natMinLen_comm (a b : Nat) :
    natMinLen a b = natMinLen b a := by
  induction a generalizing b with
  | zero =>
      cases b <;> rfl
  | succ a ih =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          exact congrArg Nat.succ (ih b)

private theorem natMaxLen_comm (a b : Nat) :
    natMaxLen a b = natMaxLen b a := by
  induction a generalizing b with
  | zero =>
      cases b <;> rfl
  | succ a ih =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          exact congrArg Nat.succ (ih b)

private theorem natMinLen_assoc (a b c : Nat) :
    natMinLen (natMinLen a b) c = natMinLen a (natMinLen b c) := by
  induction a generalizing b c with
  | zero =>
      rfl
  | succ a ih =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          cases c with
          | zero =>
              rfl
          | succ c =>
              exact congrArg Nat.succ (ih b c)

private theorem natMaxLen_assoc (a b c : Nat) :
    natMaxLen (natMaxLen a b) c = natMaxLen a (natMaxLen b c) := by
  induction a generalizing b c with
  | zero =>
      rfl
  | succ a ih =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          cases c with
          | zero =>
              rfl
          | succ c =>
              exact congrArg Nat.succ (ih b c)

private theorem natMinLen_self (a : Nat) :
    natMinLen a a = a := by
  induction a with
  | zero =>
      rfl
  | succ a ih =>
      exact congrArg Nat.succ ih

private theorem natMaxLen_self (a : Nat) :
    natMaxLen a a = a := by
  induction a with
  | zero =>
      rfl
  | succ a ih =>
      exact congrArg Nat.succ ih

private theorem natMinLen_le_left (a b : Nat) :
    natMinLen a b <= a := by
  induction a generalizing b with
  | zero =>
      exact Nat.le_refl 0
  | succ a ih =>
      cases b with
      | zero =>
          exact Nat.zero_le _
      | succ b =>
          exact Nat.succ_le_succ (ih b)

private theorem natMinLen_le_right (a b : Nat) :
    natMinLen a b <= b := by
  rw [natMinLen_comm a b]
  exact natMinLen_le_left b a

private theorem natMaxLen_left_le (a b : Nat) :
    a <= natMaxLen a b := by
  induction a generalizing b with
  | zero =>
      exact Nat.zero_le _
  | succ a ih =>
      cases b with
      | zero =>
          exact Nat.le_refl _
      | succ b =>
          exact Nat.succ_le_succ (ih b)

private theorem natMaxLen_right_le (a b : Nat) :
    b <= natMaxLen a b := by
  rw [natMaxLen_comm a b]
  exact natMaxLen_left_le b a

private theorem natMinLen_greatest {z a b : Nat} :
    z <= a -> z <= b -> z <= natMinLen a b := by
  induction z generalizing a b with
  | zero =>
      intro _ _
      exact Nat.zero_le _
  | succ z ih =>
      intro zLeA zLeB
      cases a with
      | zero =>
          cases zLeA
      | succ a =>
          cases b with
          | zero =>
              cases zLeB
          | succ b =>
              exact Nat.succ_le_succ
                (ih (Nat.le_of_succ_le_succ zLeA) (Nat.le_of_succ_le_succ zLeB))

private theorem natMaxLen_least {a b z : Nat} :
    a <= z -> b <= z -> natMaxLen a b <= z := by
  induction z generalizing a b with
  | zero =>
      intro aLeZ bLeZ
      cases a with
      | zero =>
          cases b with
          | zero =>
              exact Nat.le_refl 0
          | succ b =>
              cases bLeZ
      | succ a =>
          cases aLeZ
  | succ z ih =>
      intro aLeZ bLeZ
      cases a with
      | zero =>
          cases b with
          | zero =>
              exact Nat.zero_le _
          | succ b =>
              exact Nat.succ_le_succ (Nat.le_of_succ_le_succ bLeZ)
      | succ a =>
          cases b with
          | zero =>
              exact Nat.succ_le_succ (Nat.le_of_succ_le_succ aLeZ)
          | succ b =>
              exact Nat.succ_le_succ
                (ih (Nat.le_of_succ_le_succ aLeZ) (Nat.le_of_succ_le_succ bLeZ))

private theorem natMinLen_absorb_natMaxLen (a b : Nat) :
    natMinLen a (natMaxLen a b) = a := by
  induction a generalizing b with
  | zero =>
      rfl
  | succ a ih =>
      cases b with
      | zero =>
          exact natMinLen_self (a + 1)
      | succ b =>
          exact congrArg Nat.succ (ih b)

private theorem natMaxLen_absorb_natMinLen (a b : Nat) :
    natMaxLen a (natMinLen a b) = a := by
  induction a generalizing b with
  | zero =>
      rfl
  | succ a ih =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          exact congrArg Nat.succ (ih b)

private theorem unary_hsame_of_length_for_lattice {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem PreorderPrefixLE_of_unary_length_le {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h <= bwordLength k ->
      PreorderPrefixLE h k := by
  intro hUnary kUnary lengthLe
  have total := NatUnaryPrefix_total hUnary kUnary
  cases total with
  | inl hLeK =>
      exact hLeK
  | inr kLeH =>
      have sameHK : hsame h k := by
        apply unary_hsame_of_length_for_lattice hUnary kUnary
        have kLengthLeH : bwordLength k <= bwordLength h := by
          cases kLeH with
          | intro tail data =>
              have lengthH :
                  bwordLength h = bwordLength k + bwordLength tail :=
                NatUp_unary_standard_bridge.right.right.right.right
                  kUnary data.left data.right
              rw [lengthH]
              exact Nat.le_add_right _ _
        exact Nat.le_antisymm lengthLe kLengthLeH
      exact PreorderPrefixLE_of_hsame sameHK

theorem natMin_unary {a b : BHist} : UnaryHistory (natMin a b) := by
  exact natToUnary_unary _

theorem natMax_unary {a b : BHist} : UnaryHistory (natMax a b) := by
  exact natToUnary_unary _

theorem natLcm_unary {a b : BHist} : UnaryHistory (natLcm a b) := by
  exact natToUnary_unary _

theorem natMin_comm_hsame {a b : BHist} :
    hsame (natMin a b) (natMin b a) := by
  apply unary_hsame_of_length_for_lattice
  · exact natMin_unary
  · exact natMin_unary
  · unfold natMin
    rw [natToUnary_length, natToUnary_length]
    exact natMinLen_comm _ _

theorem natMax_comm_hsame {a b : BHist} :
    hsame (natMax a b) (natMax b a) := by
  apply unary_hsame_of_length_for_lattice
  · exact natMax_unary
  · exact natMax_unary
  · unfold natMax
    rw [natToUnary_length, natToUnary_length]
    exact natMaxLen_comm _ _

theorem natMin_assoc_hsame {a b c : BHist} :
    hsame (natMin (natMin a b) c) (natMin a (natMin b c)) := by
  apply unary_hsame_of_length_for_lattice
  · exact natMin_unary
  · exact natMin_unary
  · unfold natMin
    rw [natToUnary_length, natToUnary_length, natToUnary_length, natToUnary_length]
    exact natMinLen_assoc _ _ _

theorem natMax_assoc_hsame {a b c : BHist} :
    hsame (natMax (natMax a b) c) (natMax a (natMax b c)) := by
  apply unary_hsame_of_length_for_lattice
  · exact natMax_unary
  · exact natMax_unary
  · unfold natMax
    rw [natToUnary_length, natToUnary_length, natToUnary_length, natToUnary_length]
    exact natMaxLen_assoc _ _ _

theorem natMin_idempotent_hsame {a : BHist} :
    UnaryHistory a -> hsame (natMin a a) a := by
  intro aUnary
  apply unary_hsame_of_length_for_lattice
  · exact natMin_unary
  · exact aUnary
  · unfold natMin
    rw [natToUnary_length]
    exact natMinLen_self _

theorem natMax_idempotent_hsame {a : BHist} :
    UnaryHistory a -> hsame (natMax a a) a := by
  intro aUnary
  apply unary_hsame_of_length_for_lattice
  · exact natMax_unary
  · exact aUnary
  · unfold natMax
    rw [natToUnary_length]
    exact natMaxLen_self _

theorem natMin_le_left {a b : BHist} :
    UnaryHistory a -> PreorderPrefixLE (natMin a b) a := by
  intro aUnary
  apply PreorderPrefixLE_of_unary_length_le
  · exact natMin_unary
  · exact aUnary
  · unfold natMin
    rw [natToUnary_length]
    exact natMinLen_le_left _ _

theorem natMin_le_right {a b : BHist} :
    UnaryHistory b -> PreorderPrefixLE (natMin a b) b := by
  intro bUnary
  apply PreorderPrefixLE_of_unary_length_le
  · exact natMin_unary
  · exact bUnary
  · unfold natMin
    rw [natToUnary_length]
    exact natMinLen_le_right _ _

theorem natMax_left_le {a b : BHist} :
    UnaryHistory a -> PreorderPrefixLE a (natMax a b) := by
  intro aUnary
  apply PreorderPrefixLE_of_unary_length_le
  · exact aUnary
  · exact natMax_unary
  · unfold natMax
    rw [natToUnary_length]
    exact natMaxLen_left_le _ _

theorem natMax_right_le {a b : BHist} :
    UnaryHistory b -> PreorderPrefixLE b (natMax a b) := by
  intro bUnary
  apply PreorderPrefixLE_of_unary_length_le
  · exact bUnary
  · exact natMax_unary
  · unfold natMax
    rw [natToUnary_length]
    exact natMaxLen_right_le _ _

theorem natMin_greatest_lower_bound {a b z : BHist} :
    UnaryHistory z -> PreorderPrefixLE z a -> PreorderPrefixLE z b ->
      PreorderPrefixLE z (natMin a b) := by
  intro zUnary zLeA zLeB
  have aUnary : UnaryHistory a := PreorderPrefixLE_preserves_carrier zUnary zLeA
  have bUnary : UnaryHistory b := PreorderPrefixLE_preserves_carrier zUnary zLeB
  apply PreorderPrefixLE_of_unary_length_le zUnary natMin_unary
  unfold natMin
  rw [natToUnary_length]
  have zLeALength : bwordLength z <= bwordLength a := by
    cases zLeA with
    | intro tail data =>
        have lengthA :
            bwordLength a = bwordLength z + bwordLength tail :=
          NatUp_unary_standard_bridge.right.right.right.right zUnary data.left data.right
        rw [lengthA]
        exact Nat.le_add_right _ _
  have zLeBLength : bwordLength z <= bwordLength b := by
    cases zLeB with
    | intro tail data =>
        have lengthB :
            bwordLength b = bwordLength z + bwordLength tail :=
          NatUp_unary_standard_bridge.right.right.right.right zUnary data.left data.right
        rw [lengthB]
        exact Nat.le_add_right _ _
  exact natMinLen_greatest zLeALength zLeBLength

theorem natMax_least_upper_bound {a b z : BHist} :
    UnaryHistory z -> PreorderPrefixLE a z -> PreorderPrefixLE b z ->
      PreorderPrefixLE (natMax a b) z := by
  intro zUnary aLeZ bLeZ
  have aUnary : UnaryHistory a := PreorderPrefixLE_source_carrier_of_target_carrier aLeZ zUnary
  have bUnary : UnaryHistory b := PreorderPrefixLE_source_carrier_of_target_carrier bLeZ zUnary
  apply PreorderPrefixLE_of_unary_length_le natMax_unary zUnary
  unfold natMax
  rw [natToUnary_length]
  have aLeZLength : bwordLength a <= bwordLength z := by
    cases aLeZ with
    | intro tail data =>
        have lengthZ :
            bwordLength z = bwordLength a + bwordLength tail :=
          NatUp_unary_standard_bridge.right.right.right.right aUnary data.left data.right
        rw [lengthZ]
        exact Nat.le_add_right _ _
  have bLeZLength : bwordLength b <= bwordLength z := by
    cases bLeZ with
    | intro tail data =>
        have lengthZ :
            bwordLength z = bwordLength b + bwordLength tail :=
          NatUp_unary_standard_bridge.right.right.right.right bUnary data.left data.right
        rw [lengthZ]
        exact Nat.le_add_right _ _
  exact natMaxLen_least aLeZLength bLeZLength

theorem natMin_absorb_natMax_hsame {a b : BHist} :
    UnaryHistory a -> UnaryHistory b -> hsame (natMin a (natMax a b)) a := by
  intro aUnary _bUnary
  apply unary_hsame_of_length_for_lattice
  · exact natMin_unary
  · exact aUnary
  · unfold natMin natMax
    rw [natToUnary_length, natToUnary_length]
    exact natMinLen_absorb_natMaxLen _ _

theorem natMax_absorb_natMin_hsame {a b : BHist} :
    UnaryHistory a -> UnaryHistory b -> hsame (natMax a (natMin a b)) a := by
  intro aUnary _bUnary
  apply unary_hsame_of_length_for_lattice
  · exact natMax_unary
  · exact aUnary
  · unfold natMax natMin
    rw [natToUnary_length, natToUnary_length]
    exact natMaxLen_absorb_natMinLen _ _

theorem natMin_natMax_lattice_laws {a b c : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
      hsame (natMin a b) (natMin b a) ∧
      hsame (natMax a b) (natMax b a) ∧
      hsame (natMin (natMin a b) c) (natMin a (natMin b c)) ∧
      hsame (natMax (natMax a b) c) (natMax a (natMax b c)) ∧
      hsame (natMin a a) a ∧
      hsame (natMax a a) a ∧
      hsame (natMin a (natMax a b)) a ∧
      hsame (natMax a (natMin a b)) a := by
  intro aUnary bUnary _cUnary
  exact
    ⟨natMin_comm_hsame,
      natMax_comm_hsame,
      natMin_assoc_hsame,
      natMax_assoc_hsame,
      natMin_idempotent_hsame aUnary,
      natMax_idempotent_hsame aUnary,
      natMin_absorb_natMax_hsame aUnary bUnary,
      natMax_absorb_natMin_hsame aUnary bUnary⟩

def NatLcm (a b l : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory l ∧
    NatDivides a l ∧ NatDivides b l ∧
      ∀ m : BHist, NatDivides a m -> NatDivides b m -> NatDivides l m

theorem NatLcm_left_unary {a b l : BHist} :
    NatLcm a b l -> UnaryHistory a := by
  intro lcm
  exact lcm.left

theorem NatLcm_right_unary {a b l : BHist} :
    NatLcm a b l -> UnaryHistory b := by
  intro lcm
  exact lcm.right.left

theorem NatLcm_result_unary {a b l : BHist} :
    NatLcm a b l -> UnaryHistory l := by
  intro lcm
  exact lcm.right.right.left

theorem NatLcm_left_dvd {a b l : BHist} :
    NatLcm a b l -> NatDivides a l := by
  intro lcm
  exact lcm.right.right.right.left

theorem NatLcm_right_dvd {a b l : BHist} :
    NatLcm a b l -> NatDivides b l := by
  intro lcm
  exact lcm.right.right.right.right.left

theorem NatLcm_least {a b l m : BHist} :
    NatLcm a b l -> NatDivides a m -> NatDivides b m -> NatDivides l m := by
  intro lcm
  exact lcm.right.right.right.right.right m

theorem NatLcm_unique_hsame {a b l m : BHist} :
    NatLcm a b l -> NatLcm a b m -> hsame l m := by
  intro left right
  have lDividesM : NatDivides l m :=
    NatLcm_least left (NatLcm_left_dvd right) (NatLcm_right_dvd right)
  have mDividesL : NatDivides m l :=
    NatLcm_least right (NatLcm_left_dvd left) (NatLcm_right_dvd left)
  exact NatDivides_antisymmetry_hsame
    (NatLcm_result_unary left) (NatLcm_result_unary right) lDividesM mDividesL

theorem NatGcd_meet_for_divides {a b g : BHist} :
    NatGcd a b g ->
      NatDivides g a ∧ NatDivides g b ∧
        ∀ d : BHist, NatDivides d a -> NatDivides d b -> NatDivides d g := by
  intro gcd
  exact
    ⟨NatGcd_dvd_left gcd, NatGcd_dvd_right gcd,
      fun d dividesA dividesB => NatGcd_greatest gcd dividesA dividesB⟩

theorem NatLcm_join_for_divides {a b l : BHist} :
    NatLcm a b l ->
      NatDivides a l ∧ NatDivides b l ∧
        ∀ m : BHist, NatDivides a m -> NatDivides b m -> NatDivides l m := by
  intro lcm
  exact
    ⟨NatLcm_left_dvd lcm, NatLcm_right_dvd lcm,
      fun m dividesA dividesB => NatLcm_least lcm dividesA dividesB⟩

theorem NatGcd_divides_order_meet {a b g d : BHist} :
    NatGcd a b g ->
      (NatDivides d g ↔ NatDivides d a ∧ NatDivides d b) := by
  intro gcd
  constructor
  · intro dDividesG
    exact
      ⟨NatDivides_transitive dDividesG (NatGcd_dvd_left gcd),
        NatDivides_transitive dDividesG (NatGcd_dvd_right gcd)⟩
  · intro both
    exact NatGcd_greatest gcd both.left both.right

theorem NatLcm_divides_order_join {a b l m : BHist} :
    NatLcm a b l ->
      (NatDivides l m ↔ NatDivides a m ∧ NatDivides b m) := by
  intro lcm
  constructor
  · intro lDividesM
    exact
      ⟨NatDivides_transitive (NatLcm_left_dvd lcm) lDividesM,
        NatDivides_transitive (NatLcm_right_dvd lcm) lDividesM⟩
  · intro both
    exact NatLcm_least lcm both.left both.right

theorem NatGcd_natLcm_absorption {a b l : BHist} :
    NatLcm a b l -> NatGcd a l a := by
  intro lcm
  constructor
  · exact NatLcm_left_unary lcm
  · constructor
    · exact NatLcm_result_unary lcm
    · constructor
      · exact NatLcm_left_unary lcm
      · constructor
        · exact (NatDivides_reflexive_pair (NatLcm_left_unary lcm)).right
        · constructor
          · exact NatLcm_left_dvd lcm
          · intro d dividesA _dividesL
            exact dividesA

theorem NatGcd_natLcm_absorption_hsame {a b l g : BHist} :
    NatLcm a b l -> NatGcd a l g -> hsame g a := by
  intro lcm gcd
  exact NatGcd_unique_hsame gcd (NatGcd_natLcm_absorption lcm)

end BEDC.Derived.LatticeUp

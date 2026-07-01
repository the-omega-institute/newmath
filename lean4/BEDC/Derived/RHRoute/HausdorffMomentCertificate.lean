import BEDC.Real.RatNumKernel
import BEDC.Derived.RHRoute.CausalReflectionPositiveCone

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.HausdorffMomentCertificate

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.CausalReflectionPositiveCone

abbrev Rat : Type :=
  BEDC.Derived.RationalUp.RatNum

def cmDiff (M : Nat -> Rat) (j : Nat) : Nat -> Rat
  | 0 => M j
  | Nat.succ k => ratSub (cmDiff M j k) (cmDiff M (j + 1) k)

def checkCMPrefix (N : Nat) (M : Nat -> Rat) : Prop :=
  ∀ j k : Nat, j + k ≤ N -> ratLe ratZero (cmDiff M j k)

structure RatAtoms where
  atoms : Nat
  position : Nat -> Rat
  weight : Nat -> Rat
  position_nonneg : ∀ a : Nat, a < atoms -> ratLe ratZero (position a)
  position_le_one : ∀ a : Nat, a < atoms -> ratLe (position a) ratOne
  weight_nonneg : ∀ a : Nat, a < atoms -> ratLe ratZero (weight a)

def atomMoment (A : RatAtoms) (n : Nat) : Rat :=
  ratSum A.atoms (fun a => ratMul (A.weight a) (ratPow (A.position a) n))

structure AtomRep (N : Nat) (M : Nat -> Rat) (A : RatAtoms) : Prop where
  moment_eq : ∀ j : Nat, j ≤ N -> RatEq (M j) (atomMoment A j)

theorem ratSub_nonneg_of_ratLe {x y : Rat} :
    ratLe y x -> ratLe ratZero (ratSub x y) := by
  intro h
  exact BEDC.Derived.RationalUp.ratSub_nonneg_of_le h

theorem one_sub_nonneg_of_le_one {x : Rat} :
    ratLe x ratOne -> ratLe ratZero (ratSub ratOne x) := by
  intro h
  exact ratSub_nonneg_of_ratLe h

theorem ratMul_three_nonneg {a b c : Rat} :
    ratLe ratZero a ->
    ratLe ratZero b ->
    ratLe ratZero c ->
    ratLe ratZero (ratMul (ratMul a b) c) := by
  intro ha hb hc
  exact ratMul_nonneg (ratMul_nonneg ha hb) hc

theorem ratSum_nonneg_lt {K : Nat} {f : Nat -> Rat}
    (h : ∀ a : Nat, a < K -> ratLe ratZero (f a)) :
    ratLe ratZero (ratSum K f) := by
  induction K with
  | zero =>
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | succ K ih =>
      change ratLe ratZero (ratAdd (ratSum K f) (f K))
      have leftNonneg : ratLe ratZero (ratSum K f) := by
        apply ih
        intro a ha
        exact h a (Nat.lt_trans ha (Nat.lt_succ_self K))
      have rightNonneg : ratLe ratZero (f K) :=
        h K (Nat.lt_succ_self K)
      have raw :
          ratLe (ratAdd ratZero ratZero)
            (ratAdd (ratSum K f) (f K)) :=
        ratAdd_le_add leftNonneg rightNonneg
      exact ratLe_of_RatEq_left (ratZero_add_left ratZero) raw

theorem atom_gap_term_nonneg
    (A : RatAtoms) (a j k : Nat) (ha : a < A.atoms) :
    ratLe ratZero
      (ratMul
        (ratMul (A.weight a) (ratPow (A.position a) j))
        (ratPow (ratSub ratOne (A.position a)) k)) := by
  apply ratMul_three_nonneg
  · exact A.weight_nonneg a ha
  · exact ratPow_nonneg (A.position_nonneg a ha) j
  · exact ratPow_nonneg (one_sub_nonneg_of_le_one (A.position_le_one a ha)) k

def atomDiffMoment (A : RatAtoms) (j k : Nat) : Rat :=
  ratSum A.atoms
    (fun a =>
      ratMul
        (ratMul (A.weight a) (ratPow (A.position a) j))
        (ratPow (ratSub ratOne (A.position a)) k))

structure AtomDiffAudit (N : Nat) (M : Nat -> Rat) (A : RatAtoms) : Prop where
  diff_eq :
    ∀ j k : Nat, j + k ≤ N ->
      RatEq (cmDiff M j k) (atomDiffMoment A j k)

theorem atomDiffMoment_nonneg (A : RatAtoms) (j k : Nat) :
    ratLe ratZero (atomDiffMoment A j k) := by
  unfold atomDiffMoment
  apply ratSum_nonneg_lt
  intro a ha
  exact atom_gap_term_nonneg A a j k ha

theorem atomDiffAudit_implies_cmPrefix
    {N : Nat} {M : Nat -> Rat} {A : RatAtoms}
    (audit : AtomDiffAudit N M A) :
    checkCMPrefix N M := by
  intro j k hjk
  exact ratLe_of_RatEq_right (atomDiffMoment_nonneg A j k)
    (RatEq_symm (audit.diff_eq j k hjk))

structure AtomMomentCertificate (N : Nat) (M : Nat -> Rat) where
  atoms : RatAtoms
  rep : AtomRep N M atoms
  diff_audit : AtomDiffAudit N M atoms

theorem atomRep_gives_cmPrefix
    {N : Nat} {M : Nat -> Rat} {A : RatAtoms}
    (_h : AtomRep N M A)
    (audit : AtomDiffAudit N M A) :
    checkCMPrefix N M := by
  exact atomDiffAudit_implies_cmPrefix audit

theorem atomMomentCertificate_sound
    {N : Nat} {M : Nat -> Rat}
    (C : AtomMomentCertificate N M) :
    checkCMPrefix N M :=
  atomRep_gives_cmPrefix C.rep C.diff_audit

def badM : Nat -> Rat
  | 0 => ratAdd ratOne ratOne
  | 1 => ratOne
  | _ => ratZero

theorem ratOne_nonneg_local :
    ratLe ratZero ratOne :=
  ratNat_nonneg 1

theorem ratOne_add_ratOne_nonneg :
    ratLe ratZero (ratAdd ratOne ratOne) := by
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd ratOne ratOne) :=
    ratAdd_le_add ratOne_nonneg_local ratOne_nonneg_local
  exact ratLe_of_RatEq_left (ratZero_add_left ratZero) raw

theorem badM_diff_zero_one :
    RatEq (cmDiff badM 0 1) ratOne := by
  change RatEq (ratSub (ratAdd ratOne ratOne) ratOne) ratOne
  exact ratSub_eq_of_add_right_eq (RatEq_refl (ratAdd ratOne ratOne))

theorem badM_diff_one_one :
    RatEq (cmDiff badM 1 1) ratOne := by
  change RatEq (ratSub ratOne ratZero) ratOne
  exact ratSub_eq_of_add_right_eq (ratAdd_zero_right ratOne)

theorem badM_diff_zero_two :
    RatEq (cmDiff badM 0 2) ratZero := by
  change RatEq
    (ratSub (cmDiff badM 0 1) (cmDiff badM 1 1))
    ratZero
  exact (ratSub_zero_iff (cmDiff badM 0 1) (cmDiff badM 1 1)).mpr
    (RatEq_trans _ _ _ badM_diff_zero_one (RatEq_symm badM_diff_one_one))

theorem badM_cm_prefix :
    checkCMPrefix 2 badM := by
  intro j k hjk
  cases k with
  | zero =>
      cases j with
      | zero =>
          change ratLe ratZero (ratAdd ratOne ratOne)
          exact ratOne_add_ratOne_nonneg
      | succ j =>
          cases j with
          | zero =>
              change ratLe ratZero ratOne
              exact ratOne_nonneg_local
          | succ j =>
              cases j with
              | zero =>
                  change ratLe ratZero ratZero
                  exact ratLe_refl ratZero
              | succ j =>
                  exfalso
                  omega
  | succ k =>
      cases k with
      | zero =>
          cases j with
          | zero =>
              exact ratLe_of_RatEq_right ratOne_nonneg_local
                (RatEq_symm badM_diff_zero_one)
          | succ j =>
              cases j with
              | zero =>
                  exact ratLe_of_RatEq_right ratOne_nonneg_local
                    (RatEq_symm badM_diff_one_one)
              | succ j =>
                  exfalso
                  omega
      | succ k =>
          cases k with
          | zero =>
              cases j with
              | zero =>
                  exact ratLe_of_RatEq_right (ratLe_refl ratZero)
                    (RatEq_symm badM_diff_zero_two)
              | succ j =>
                  exfalso
                  omega
          | succ k =>
              exfalso
              omega

def twoAtomShape (A : RatAtoms) : Prop :=
  A.atoms = 2

theorem badM_no_two_atom
    (A : RatAtoms)
    (_shape : twoAtomShape A)
    (_rep : AtomRep 2 badM A)
    (second_moment_forces_first_zero :
      RatEq (badM 2) ratZero ->
        RatEq (badM 1) ratZero) :
    False := by
  have h2 : RatEq (badM 2) ratZero := by
    exact RatEq_refl ratZero
  have h1zero : RatEq (badM 1) ratZero :=
    second_moment_forces_first_zero h2
  have hOnePos : ratLt ratZero ratOne := by
    exact BEDC.Real.RatNumLogEnclosure.ratOne_pos
  exact ratLt_not_RatEq hOnePos (RatEq_symm h1zero)

theorem counterexample_finite_cm_not_sufficient :
    checkCMPrefix 2 badM ∧
      (∀ A : RatAtoms,
        twoAtomShape A ->
        AtomRep 2 badM A ->
        (RatEq (badM 2) ratZero -> RatEq (badM 1) ratZero) ->
        False) := by
  exact ⟨badM_cm_prefix, badM_no_two_atom⟩

def toyAtoms : RatAtoms where
  atoms := 2
  position := fun a =>
    match a with
    | 0 => ratZero
    | _ => ratOne
  weight := fun a =>
    match a with
    | 0 => ratOne
    | _ => ratOne
  position_nonneg := by
    intro a ha
    cases a with
    | zero => exact ratLe_refl ratZero
    | succ a =>
        cases a with
        | zero =>
            change ratLe ratZero ratOne
            exact ratNat_nonneg 1
        | succ a =>
            omega
  position_le_one := by
    intro a ha
    cases a with
    | zero =>
        change ratLe ratZero ratOne
        exact ratNat_nonneg 1
    | succ a =>
        cases a with
        | zero => exact ratLe_refl ratOne
        | succ a =>
            omega
  weight_nonneg := by
    intro a _ha
    cases a <;> change ratLe ratZero ratOne
    · exact ratNat_nonneg 1
    · exact ratNat_nonneg 1

def toyM (n : Nat) : Rat :=
  atomMoment toyAtoms n

theorem toyAtoms_atomRep :
    AtomRep 2 toyM toyAtoms := by
  constructor
  intro j _hj
  exact RatEq_refl (toyM j)

theorem toyAtoms_cmPrefix
    (audit : AtomDiffAudit 2 toyM toyAtoms) :
    checkCMPrefix 2 toyM :=
  atomRep_gives_cmPrefix toyAtoms_atomRep audit

structure FinalMomentObligationCore where
  trueMoment : Nat -> Rat
  source_prefix : Nat -> Prop
  all_finite_cm : ∀ N : Nat, checkCMPrefix N trueMoment
  xi_binding : Prop
  critical_strip_continuation : Prop
  moment_kernel_to_CRPC : CausalReflectionPositiveCone

theorem FinalMomentObligationCore.implies_RH
    (O : FinalMomentObligationCore) :
    ConstructiveRH :=
  CRPC_implies_RH O.moment_kernel_to_CRPC

end BEDC.Derived.RHRoute.HausdorffMomentCertificate

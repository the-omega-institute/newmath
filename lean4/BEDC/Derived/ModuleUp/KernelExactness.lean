import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ModuleSingletonSmul_kernel_exactness {h k : BHist} :
    ((ModuleSingletonCarrier h ∧
      ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty h) BHist.Empty) ↔
      ModuleSingletonCarrier h) ∧
      ((((ModuleSingletonCarrier h ∧
        ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty h) BHist.Empty) ∧
        (ModuleSingletonCarrier k ∧
          ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty k) BHist.Empty) ∧
        ModuleSingletonClassifier h k) ↔ ModuleSingletonClassifier h k)) := by
  constructor
  · constructor
    · intro data
      exact data.left
    · intro carrierH
      exact And.intro carrierH
        (Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))
  · constructor
    · intro data
      exact data.right.right
    · intro classified
      have emptyClassified : ModuleSingletonClassifier BHist.Empty BHist.Empty :=
        Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
      exact And.intro (And.intro classified.left emptyClassified)
        (And.intro (And.intro classified.right.left emptyClassified) classified)

theorem ModuleSingletonSmul_kernel_semanticNameCert :
    SemanticNameCert
      (fun h : BHist => ModuleSingletonCarrier h ∧
        ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty h) BHist.Empty)
      (fun h : BHist => ModuleSingletonCarrier h ∧
        ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty h) BHist.Empty)
      (fun h : BHist => ModuleSingletonCarrier h ∧
        ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty h) BHist.Empty)
      (fun h k : BHist => (ModuleSingletonCarrier h ∧
        ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty h) BHist.Empty) ∧
        (ModuleSingletonCarrier k ∧
          ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty k) BHist.Empty) ∧
        ModuleSingletonClassifier h k) := by
  have emptyCarrier : ModuleSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact {
    core := {
      carrier_inhabited := by
        have kernelExact :=
          ModuleSingletonSmul_kernel_exactness (h := BHist.Empty) (k := BHist.Empty)
        exact Exists.intro BHist.Empty (Iff.mpr kernelExact.left emptyCarrier)
      equiv_refl := by
        intro h source
        have kernelExact := ModuleSingletonSmul_kernel_exactness (h := h) (k := h)
        have carrierH : ModuleSingletonCarrier h := Iff.mp kernelExact.left source
        have classifiedHH : ModuleSingletonClassifier h h :=
          BEDC.FKernel.NameCert.NameCert.equiv_refl
            singleton_empty_history_module_laws.left.core carrierH
        exact And.intro source (And.intro source classifiedHH)
      equiv_symm := by
        intro h k same
        have classifiedKH : ModuleSingletonClassifier k h :=
          BEDC.FKernel.NameCert.NameCert.equiv_symm
            singleton_empty_history_module_laws.left.core same.right.right
        exact And.intro same.right.left (And.intro same.left classifiedKH)
      equiv_trans := by
        intro h k r sameHK sameKR
        have classifiedHR : ModuleSingletonClassifier h r :=
          BEDC.FKernel.NameCert.NameCert.equiv_trans
            singleton_empty_history_module_laws.left.core sameHK.right.right sameKR.right.right
        exact And.intro sameHK.left (And.intro sameKR.right.left classifiedHR)
      carrier_respects_equiv := by
        intro h k same _sourceH
        have kernelExact := ModuleSingletonSmul_kernel_exactness (h := k) (k := h)
        have carrierK : ModuleSingletonCarrier k := same.right.right.right.left
        exact Iff.mpr kernelExact.left carrierK
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

theorem ModuleParitySmul_epsilon_boolean_orbit_involutive {m : BHist} :
    (hsame m BHist.Empty ∨ hsame m ModuleParityOne) ->
      hsame (ModuleParitySmul ModuleParityEps (ModuleParitySmul ModuleParityEps m)) m := by
  intro booleanEndpoint
  cases booleanEndpoint with
  | inl emptyM =>
      cases emptyM
      exact hsame_refl BHist.Empty
  | inr oneM =>
      cases oneM
      exact hsame_refl ModuleParityOne

end BEDC.Derived.ModuleUp

import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist

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

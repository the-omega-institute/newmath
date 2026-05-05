import BEDC.Derived.ModuleUp

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist

theorem ModuleSingletonSmul_kernel_submodule_closure {r : BHist} :
    ModuleSingletonCarrier r ->
      (let Kernel := fun x : BHist =>
        ModuleSingletonCarrier x ∧
          ModuleSingletonClassifier (ModuleSingletonSmul r x) BHist.Empty
      Kernel ModuleSingletonZero ∧
        (∀ {x y : BHist}, Kernel x -> Kernel y -> Kernel (ModuleSingletonAdd x y)) ∧
          (∀ {x : BHist}, Kernel x -> Kernel (ModuleSingletonNeg x)) ∧
            (∀ {s x : BHist}, ModuleSingletonCarrier s -> Kernel x ->
              Kernel (ModuleSingletonSmul s x)) ∧
              (∀ {x y : BHist}, Kernel x -> ModuleSingletonClassifier x y -> Kernel y)) := by
  intro _carrierR
  dsimp
  have emptyCarrier : ModuleSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyKernelClassifier :
      ModuleSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact And.intro emptyCarrier emptyKernelClassifier
  · constructor
    · intro x y _kernelX _kernelY
      exact And.intro emptyCarrier emptyKernelClassifier
    · constructor
      · intro x _kernelX
        exact And.intro emptyCarrier emptyKernelClassifier
      · constructor
        · intro s x _carrierS _kernelX
          exact And.intro emptyCarrier emptyKernelClassifier
        · intro x y kernelX classifiedXY
          have yCarrier : ModuleSingletonCarrier y := classifiedXY.right.left
          have yKernelClassifier : ModuleSingletonClassifier (ModuleSingletonSmul r y) BHist.Empty :=
            Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
              (And.intro emptyCarrier emptyCarrier)
          exact And.intro yCarrier yKernelClassifier

end BEDC.Derived.ModuleUp

import BEDC.Derived.RealCauchyCompletionUp.FamilyTailSynchronization
import BEDC.Derived.RealCauchyCompletionUp.NullTailBudgetCorrespondence

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_synchronized_null_tail_consumer [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert family'
      modulus' diagonal' window' readback' dyadic' sealRow' provenance' localCert' nullTail
      dyadicBudget zeroTailSurface equalitySurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg →
      RealCauchyCompletionCarrier family' modulus' diagonal' window' readback' dyadic'
          sealRow' provenance' localCert' bundle pkg →
        hsame family family' →
          hsame modulus modulus' →
            hsame window window' →
              hsame dyadic dyadic' →
                UnaryHistory nullTail →
                  Cont readback nullTail dyadicBudget →
                    Cont dyadicBudget sealRow zeroTailSurface →
                      Cont zeroTailSurface sealRow' equalitySurface →
                        PkgSig bundle zeroTailSurface pkg →
                          PkgSig bundle equalitySurface pkg →
                            hsame readback readback' ∧ hsame sealRow sealRow' ∧
                              UnaryHistory dyadicBudget ∧ UnaryHistory zeroTailSurface ∧
                                UnaryHistory equalitySurface ∧
                                  Cont readback nullTail dyadicBudget ∧
                                    Cont dyadicBudget sealRow zeroTailSurface ∧
                                      Cont zeroTailSurface sealRow' equalitySurface ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle provenance' pkg ∧
                                            PkgSig bundle zeroTailSurface pkg ∧
                                              PkgSig bundle equalitySurface pkg := by
  intro carrier carrier' sameFamily sameModulus sameWindow sameDyadic
  intro nullTailUnary readbackNullTailBudget budgetSealSurface surfaceSealEquality
  intro zeroTailSurfacePkg equalitySurfacePkg
  have synchronized :=
    RealCauchyCompletionCarrier_family_tail_synchronization
      (family := family) (modulus := modulus) (diagonal := diagonal) (window := window)
      (readback := readback) (dyadic := dyadic) (sealRow := sealRow)
      (provenance := provenance) (localCert := localCert) (family' := family')
      (modulus' := modulus') (diagonal' := diagonal') (window' := window')
      (readback' := readback') (dyadic' := dyadic') (sealRow' := sealRow')
      (provenance' := provenance') (localCert' := localCert') (bundle := bundle)
      (pkg := pkg) carrier carrier' sameFamily sameModulus sameWindow sameDyadic
  have budgeted :=
    RealCauchyCompletionCarrier_null_tail_budget_correspondence
      (family := family) (modulus := modulus) (diagonal := diagonal) (window := window)
      (readback := readback) (dyadic := dyadic) (sealRow := sealRow)
      (provenance := provenance) (localCert := localCert) (nullTail := nullTail)
      (dyadicBudget := dyadicBudget) (zeroTailSurface := zeroTailSurface)
      (bundle := bundle) (pkg := pkg) carrier nullTailUnary readbackNullTailBudget
      budgetSealSurface zeroTailSurfacePkg
  obtain ⟨sameReadback, sameSeal, _sealUnary, sealUnary', provenancePkg,
    provenancePkg'⟩ := synchronized
  obtain ⟨_readbackUnary, _sealUnaryBudget, dyadicBudgetUnary, zeroTailSurfaceUnary,
    readbackNullTailBudgetRow, budgetSealSurfaceRow, _provenancePkgBudget,
    zeroTailSurfacePkgRow⟩ := budgeted
  have equalitySurfaceUnary : UnaryHistory equalitySurface :=
    unary_cont_closed zeroTailSurfaceUnary sealUnary' surfaceSealEquality
  exact
    ⟨sameReadback, sameSeal, dyadicBudgetUnary, zeroTailSurfaceUnary, equalitySurfaceUnary,
      readbackNullTailBudgetRow, budgetSealSurfaceRow, surfaceSealEquality, provenancePkg,
      provenancePkg', zeroTailSurfacePkgRow, equalitySurfacePkg⟩

end BEDC.Derived.RealCauchyCompletionUp

import BEDC.Derived.MetaCICClosurePreservationUp.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem MetaCICClosurePreservationCarrier_generator_route [AskSetup] [PackageSetup]
    {S V U B F A C G R H Q P N betaConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosurePreservationCarrier S V U B F A C G R H Q P N bundle pkg →
      Cont G B betaConsumer →
        PkgSig bundle betaConsumer pkg →
          NameCert (MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N)
              hsame ∧
            MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N G ∧
              MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N R ∧
                Cont S A Q ∧ Cont U B F ∧ Cont C G R ∧
                  Cont G B betaConsumer ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle betaConsumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame NameCert
  intro carrier betaRoute betaPkg
  have obligations :=
    MetaCICClosurePreservationCarrier_namecert_obligations
      (S := S) (V := V) (U := U) (B := B) (F := F) (A := A) (C := C)
      (G := G) (R := R) (H := H) (Q := Q) (P := P) (N := N)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨cert, routeSAQ, routeUBF, routeCGR, pPkg, nPkg⟩ := obligations
  exact
    ⟨cert, MetaCICClosurePreservationRowSource.generatorClassifier,
      MetaCICClosurePreservationRowSource.subjectReductionConsumer, routeSAQ, routeUBF,
      routeCGR, betaRoute, pPkg, nPkg, betaPkg⟩

end BEDC.Derived.MetaCICClosurePreservationUp

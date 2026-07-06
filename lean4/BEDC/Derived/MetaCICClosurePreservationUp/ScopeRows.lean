import BEDC.Derived.MetaCICClosurePreservationUp.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem MetaCICClosurePreservationCarrier_scope_rows [AskSetup] [PackageSetup]
    {S V U B F A C G R H Q P N betaConsumer candidateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosurePreservationCarrier S V U B F A C G R H Q P N bundle pkg →
      Cont G B betaConsumer →
        Cont R G candidateRead →
          PkgSig bundle betaConsumer pkg →
            PkgSig bundle candidateRead pkg →
              MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N A ∧
                MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N C ∧
                  MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N G ∧
                    MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N R ∧
                      MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N P ∧
                        Cont S A Q ∧ Cont U B F ∧ Cont C G R ∧
                          Cont G B betaConsumer ∧ Cont R G candidateRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                              PkgSig bundle betaConsumer pkg ∧
                                PkgSig bundle candidateRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig
  intro carrier betaRoute candidateRoute betaPkg candidatePkg
  have obligations :=
    MetaCICClosurePreservationCarrier_namecert_obligations
      (S := S) (V := V) (U := U) (B := B) (F := F) (A := A) (C := C)
      (G := G) (R := R) (H := H) (Q := Q) (P := P) (N := N)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨_cert, routeSAQ, routeUBF, routeCGR, pPkg, nPkg⟩ := obligations
  exact
    ⟨MetaCICClosurePreservationRowSource.auditRow,
      MetaCICClosurePreservationRowSource.closedSeal,
      MetaCICClosurePreservationRowSource.generatorClassifier,
      MetaCICClosurePreservationRowSource.subjectReductionConsumer,
      MetaCICClosurePreservationRowSource.provenance, routeSAQ, routeUBF, routeCGR,
      betaRoute, candidateRoute, pPkg, nPkg, betaPkg, candidatePkg⟩

end BEDC.Derived.MetaCICClosurePreservationUp

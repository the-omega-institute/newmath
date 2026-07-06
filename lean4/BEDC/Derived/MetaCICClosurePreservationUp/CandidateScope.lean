import BEDC.Derived.MetaCICClosurePreservationUp.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem MetaCICClosurePreservationCarrier_candidate_mediated_scope [AskSetup] [PackageSetup]
    {S V U B F A C G R H Q P N candidateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosurePreservationCarrier S V U B F A C G R H Q P N bundle pkg →
      Cont A C G →
        Cont C G R →
          Cont R G candidateRead →
            PkgSig bundle candidateRead pkg →
              MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N A ∧
                MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N C ∧
                  MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N G ∧
                    MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N R ∧
                      Cont A C G ∧ Cont C G R ∧ Cont R G candidateRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle candidateRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig
  intro carrier auditSealGenerator sealGeneratorConsumer candidateRoute candidatePkg
  have obligations :=
    MetaCICClosurePreservationCarrier_namecert_obligations
      (S := S) (V := V) (U := U) (B := B) (F := F) (A := A) (C := C)
      (G := G) (R := R) (H := H) (Q := Q) (P := P) (N := N)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨_cert, _routeSAQ, _routeUBF, _routeCGR, pPkg, nPkg⟩ := obligations
  exact
    ⟨MetaCICClosurePreservationRowSource.auditRow,
      MetaCICClosurePreservationRowSource.closedSeal,
      MetaCICClosurePreservationRowSource.generatorClassifier,
      MetaCICClosurePreservationRowSource.subjectReductionConsumer,
      auditSealGenerator, sealGeneratorConsumer, candidateRoute, pPkg, nPkg, candidatePkg⟩

end BEDC.Derived.MetaCICClosurePreservationUp

import BEDC.Derived.MetaCICClosurePreservationUp.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem MetaCICClosurePreservationCarrier_subject_reduction_boundary [AskSetup] [PackageSetup]
    {S V U B F A C G R H Q P N subjectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosurePreservationCarrier S V U B F A C G R H Q P N bundle pkg →
      Cont C G subjectRead →
        PkgSig bundle subjectRead pkg →
          NameCert (MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N)
              hsame ∧
            MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N C ∧
              MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N G ∧
                MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N R ∧
                  Cont C G R ∧ Cont C G subjectRead ∧ hsame R subjectRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle subjectRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame NameCert
  intro carrier subjectRoute subjectPkg
  have obligations :=
    MetaCICClosurePreservationCarrier_namecert_obligations
      (S := S) (V := V) (U := U) (B := B) (F := F) (A := A) (C := C)
      (G := G) (R := R) (H := H) (Q := Q) (P := P) (N := N)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨cert, _routeSAQ, _routeUBF, routeCGR, pPkg, nPkg⟩ := obligations
  have sameSubject : hsame R subjectRead :=
    cont_respects_hsame (hsame_refl C) (hsame_refl G) routeCGR subjectRoute
  exact
    ⟨cert, MetaCICClosurePreservationRowSource.closedSeal,
      MetaCICClosurePreservationRowSource.generatorClassifier,
      MetaCICClosurePreservationRowSource.subjectReductionConsumer, routeCGR,
      subjectRoute, sameSubject, pPkg, nPkg, subjectPkg⟩

end BEDC.Derived.MetaCICClosurePreservationUp

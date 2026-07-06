import BEDC.Derived.MetaCICClosurePreservationUp.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem MetaCICClosurePreservationCarrier_obligation_closure [AskSetup] [PackageSetup]
    {S V U B F A C G R H Q P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosurePreservationCarrier S V U B F A C G R H Q P N bundle pkg →
      NameCert (MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N)
          hsame ∧
        MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N S ∧
          MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N V ∧
            MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N U ∧
              MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N B ∧
                MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N F ∧
                  MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N A ∧
                    MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N C ∧
                      MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N G ∧
                        MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N R ∧
                          MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N H ∧
                            MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N Q ∧
                              MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N P ∧
                                MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N N ∧
                                  Cont S A Q ∧ Cont U B F ∧ Cont C G R ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame NameCert
  intro carrier
  have obligations :=
    MetaCICClosurePreservationCarrier_namecert_obligations
      (S := S) (V := V) (U := U) (B := B) (F := F) (A := A) (C := C)
      (G := G) (R := R) (H := H) (Q := Q) (P := P) (N := N)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨cert, routeSAQ, routeUBF, routeCGR, pPkg, nPkg⟩ := obligations
  exact
    ⟨cert, MetaCICClosurePreservationRowSource.shiftClosed,
      MetaCICClosurePreservationRowSource.varSubstClosed,
      MetaCICClosurePreservationRowSource.substClosed,
      MetaCICClosurePreservationRowSource.betaClosed,
      MetaCICClosurePreservationRowSource.betaStarClosed,
      MetaCICClosurePreservationRowSource.auditRow,
      MetaCICClosurePreservationRowSource.closedSeal,
      MetaCICClosurePreservationRowSource.generatorClassifier,
      MetaCICClosurePreservationRowSource.subjectReductionConsumer,
      MetaCICClosurePreservationRowSource.transport,
      MetaCICClosurePreservationRowSource.route,
      MetaCICClosurePreservationRowSource.provenance,
      MetaCICClosurePreservationRowSource.localName, routeSAQ, routeUBF, routeCGR, pPkg,
      nPkg⟩

end BEDC.Derived.MetaCICClosurePreservationUp

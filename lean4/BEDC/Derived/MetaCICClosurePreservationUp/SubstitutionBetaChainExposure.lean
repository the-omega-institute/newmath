import BEDC.Derived.MetaCICClosurePreservationUp.TasteGate

namespace BEDC.Derived.MetaCICClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem MetaCICClosurePreservationCarrier_substitution_beta_chain_exposure
    [AskSetup] [PackageSetup]
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
                    MetaCICClosurePreservationRowSource S V U B F A C G R H Q P N G ∧
                      Cont S A Q ∧ Cont U B F ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig NameCert hsame
  intro carrier
  have obligations :=
    MetaCICClosurePreservationCarrier_namecert_obligations
      (S := S) (V := V) (U := U) (B := B) (F := F) (A := A) (C := C)
      (G := G) (R := R) (H := H) (Q := Q) (P := P) (N := N)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨cert, routeSAQ, routeUBF, _routeCGR, pPkg, nPkg⟩ := obligations
  exact
    ⟨cert, MetaCICClosurePreservationRowSource.shiftClosed,
      MetaCICClosurePreservationRowSource.varSubstClosed,
      MetaCICClosurePreservationRowSource.substClosed,
      MetaCICClosurePreservationRowSource.betaClosed,
      MetaCICClosurePreservationRowSource.betaStarClosed,
      MetaCICClosurePreservationRowSource.auditRow,
      MetaCICClosurePreservationRowSource.generatorClassifier, routeSAQ, routeUBF, pPkg,
      nPkg⟩

end BEDC.Derived.MetaCICClosurePreservationUp

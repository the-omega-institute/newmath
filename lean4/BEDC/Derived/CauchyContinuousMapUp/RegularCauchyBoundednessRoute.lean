import BEDC.Derived.CauchyContinuousMapUp

namespace BEDC.Derived.CauchyContinuousMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived

theorem CauchyContinuousMap_regular_cauchy_boundedness_route [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp) {windowTolerance imageRead sealRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.toleranceLedger windowTolerance →
        Cont windowTolerance M.imageReadback imageRead →
          Cont imageRead M.realSealHandoff sealRead →
            Cont sealRead M.toleranceLedger boundedRead →
              PkgSig bundle boundedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M.windows ∨ hsame row M.imageReadback ∨
                        hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                          hsame row boundedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M.windows M.toleranceLedger windowTolerance ∧
                        Cont windowTolerance M.imageReadback imageRead ∧
                          Cont imageRead M.realSealHandoff sealRead ∧
                            Cont sealRead M.toleranceLedger boundedRead ∧
                              PkgSig bundle boundedRead pkg)
                    hsame ∧
                  UnaryHistory boundedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro packet windowRoute imageRoute sealRoute boundedRoute boundedPkg
  obtain ⟨windowsUnary, imageReadbackUnary, toleranceUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg⟩ := packet
  have windowToleranceUnary : UnaryHistory windowTolerance :=
    unary_cont_closed windowsUnary toleranceUnary windowRoute
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowToleranceUnary imageReadbackUnary imageRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary realSealUnary sealRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed sealUnary toleranceUnary boundedRoute
  have sourceBounded :
      (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row) boundedRead :=
    ⟨hsame_refl boundedRead, boundedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row boundedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.toleranceLedger windowTolerance ∧
              Cont windowTolerance M.imageReadback imageRead ∧
                Cont imageRead M.realSealHandoff sealRead ∧
                  Cont sealRead M.toleranceLedger boundedRead ∧
                    PkgSig bundle boundedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedRead sourceBounded
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, imageRoute, sealRoute, boundedRoute,
          boundedPkg⟩
  }
  exact ⟨cert, boundedUnary⟩

end BEDC.Derived.CauchyContinuousMapUp

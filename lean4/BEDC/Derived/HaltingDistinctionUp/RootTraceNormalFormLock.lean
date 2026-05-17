import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootTraceNormalFormLock [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead normalRead lockRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont traceRead classifier normalRead →
          Cont normalRead provenance lockRead →
            PkgSig bundle lockRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row cert ∧
                      HaltingDistinctionCarrier question trace diagonal halt classifier route
                        provenance cert bundle pkg)
                  (fun row : BHist =>
                    hsame row cert ∧ UnaryHistory row ∧ Cont trace route traceRead ∧
                      Cont traceRead classifier normalRead)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle lockRead pkg ∧
                      Cont normalRead provenance lockRead)
                  hsame ∧
                UnaryHistory traceRead ∧ UnaryHistory normalRead ∧ UnaryHistory lockRead ∧
                  Cont trace route traceRead ∧ Cont traceRead classifier normalRead ∧
                    Cont normalRead provenance lockRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle lockRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier traceRouteRead traceClassifierNormal normalProvenanceLock lockPkg
  have carrierPacket :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨_questionUnary, traceUnary, _diagonalUnary, _haltUnary, classifierUnary,
    routeUnary, provenanceUnary, certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed traceReadUnary classifierUnary traceClassifierNormal
  have lockReadUnary : UnaryHistory lockRead :=
    unary_cont_closed normalReadUnary provenanceUnary normalProvenanceLock
  have sourceAtCert :
      hsame cert cert ∧
        HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
          bundle pkg :=
    And.intro (hsame_refl cert) carrierPacket
  have certObject :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cert ∧
              HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
                cert bundle pkg)
          (fun row : BHist =>
            hsame row cert ∧ UnaryHistory row ∧ Cont trace route traceRead ∧
              Cont traceRead classifier normalRead)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle lockRead pkg ∧
              Cont normalRead provenance lockRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro cert sourceAtCert
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
          intro _row _other sameRows sourceRow
          exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            sourceRow.right
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.left, unary_transport certUnary (hsame_symm sourceRow.left),
            traceRouteRead, traceClassifierNormal⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨provenancePkg, lockPkg, normalProvenanceLock⟩
    }
  exact
    ⟨certObject, traceReadUnary, normalReadUnary, lockReadUnary, traceRouteRead,
      traceClassifierNormal, normalProvenanceLock, provenancePkg, lockPkg⟩

end BEDC.Derived.HaltingDistinctionUp

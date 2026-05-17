import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootDiagonalRouteTotality [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert diagonalRead classifierRead
      endpoint rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont diagonal halt diagonalRead →
        Cont classifier route classifierRead →
          Cont diagonalRead classifierRead endpoint →
            Cont cert provenance rootRead →
              PkgSig bundle endpoint pkg →
                PkgSig bundle rootRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        HaltingDistinctionCarrier question trace diagonal halt classifier route
                          provenance cert bundle pkg ∧ hsame row endpoint)
                      (fun row : BHist =>
                        hsame row endpoint ∧ UnaryHistory row ∧
                          Cont diagonalRead classifierRead endpoint)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                          hsame row endpoint)
                      hsame ∧
                    UnaryHistory diagonalRead ∧ UnaryHistory classifierRead ∧
                      UnaryHistory endpoint ∧ UnaryHistory rootRead ∧
                        Cont diagonal halt diagonalRead ∧
                          Cont classifier route classifierRead ∧
                            Cont diagonalRead classifierRead endpoint ∧
                              Cont cert provenance rootRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle endpoint pkg ∧
                                    PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier diagonalHaltRead classifierRouteRead readEndpoint certProvenanceRoot
    endpointPkg rootPkg
  have carrierPacket :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨_questionUnary, _traceUnary, diagonalUnary, haltUnary, classifierUnary,
    routeUnary, provenanceUnary, certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltRead
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed diagonalReadUnary classifierReadUnary readEndpoint
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed certUnary provenanceUnary certProvenanceRoot
  have certObject :
      SemanticNameCert
          (fun row : BHist =>
            HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
              cert bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            hsame row endpoint ∧ UnaryHistory row ∧ Cont diagonalRead classifierRead endpoint)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
              hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨carrierPacket, hsame_refl endpoint⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, unary_transport endpointUnary (hsame_symm source.right),
        readEndpoint⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, endpointPkg, source.right⟩
  }
  exact
    ⟨certObject, diagonalReadUnary, classifierReadUnary, endpointUnary, rootReadUnary,
      diagonalHaltRead, classifierRouteRead, readEndpoint, certProvenanceRoot, provenancePkg,
      endpointPkg, rootPkg⟩

end BEDC.Derived.HaltingDistinctionUp

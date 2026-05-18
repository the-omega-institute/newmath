import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootLedgerNonescape [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert obstructionRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont classifier route obstructionRead →
        Cont obstructionRead provenance ledgerRead →
          PkgSig bundle ledgerRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row cert ∧
                    HaltingDistinctionCarrier question trace diagonal halt classifier route
                      provenance cert bundle pkg)
                (fun row : BHist =>
                  hsame row cert ∧ UnaryHistory row ∧ Cont classifier route obstructionRead)
                (fun _row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                    Cont obstructionRead provenance ledgerRead)
                hsame ∧
              UnaryHistory cert ∧ UnaryHistory obstructionRead ∧ UnaryHistory ledgerRead ∧
                Cont classifier route obstructionRead ∧
                  Cont obstructionRead provenance ledgerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier classifierRouteObstruction obstructionProvenanceLedger ledgerPkg
  have carrierPacket :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨_questionUnary, _traceUnary, _diagonalUnary, _haltUnary, classifierUnary,
    routeUnary, provenanceUnary, certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed classifierUnary routeUnary classifierRouteObstruction
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed obstructionReadUnary provenanceUnary obstructionProvenanceLedger
  have sourceAtCert :
      hsame cert cert ∧
        HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
          bundle pkg :=
    ⟨hsame_refl cert, carrierPacket⟩
  have certObject :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cert ∧
              HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
                cert bundle pkg)
          (fun row : BHist =>
            hsame row cert ∧ UnaryHistory row ∧ Cont classifier route obstructionRead)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
              Cont obstructionRead provenance ledgerRead)
          hsame := {
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
        intro _row _other sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, unary_transport certUnary (hsame_symm source.left),
          classifierRouteObstruction⟩
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, ledgerPkg, obstructionProvenanceLedger⟩
  }
  exact
    ⟨certObject, certUnary, obstructionReadUnary, ledgerReadUnary,
      classifierRouteObstruction, obstructionProvenanceLedger, provenancePkg, ledgerPkg⟩

end BEDC.Derived.HaltingDistinctionUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContinuationTerminationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationTerminationCarrier_terminal_route [AskSetup] [PackageSetup]
    {start terminal trace witness behavior transport provenance localName terminalRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory start →
      UnaryHistory trace →
        UnaryHistory witness →
          UnaryHistory behavior →
            UnaryHistory provenance →
              UnaryHistory localName →
                Cont start trace terminalRead →
                  Cont terminalRead witness namedRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row start ∨ hsame row terminal ∨ hsame row trace ∨
                                hsame row witness ∨ hsame row behavior ∨
                                  hsame row transport ∨ hsame row provenance ∨
                                    hsame row localName ∨ hsame row terminalRead ∨
                                      hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont start trace terminalRead ∧
                                Cont terminalRead witness namedRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory terminalRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro startUnary traceUnary witnessUnary _behaviorUnary _provenanceUnary _localNameUnary
    terminalRoute namedRoute provenancePkg localNamePkg
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed startUnary traceUnary terminalRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed terminalReadUnary witnessUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, terminalRoute, namedRoute, provenancePkg, localNamePkg⟩
    }
  · exact ⟨terminalReadUnary, namedReadUnary⟩

end BEDC.Derived.ContinuationTerminationUp

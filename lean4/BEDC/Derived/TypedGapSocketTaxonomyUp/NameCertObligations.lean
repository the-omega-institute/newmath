import BEDC.Derived.TypedGapSocketTaxonomyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TypedGapSocketTaxonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TypedGapSocketTaxonomyNameCertObligations [AskSetup] [PackageSetup]
    {kind gate matrix ledger transport replay provenance localName kindGateRead
      matrixLedgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory kind →
      UnaryHistory gate →
        UnaryHistory matrix →
          UnaryHistory ledger →
            UnaryHistory replay →
              UnaryHistory localName →
                Cont kind gate kindGateRead →
                  Cont matrix ledger matrixLedgerRead →
                    Cont replay localName namedRead →
                      PkgSig bundle namedRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row kindGateRead ∨ hsame row matrixLedgerRead ∨
                                hsame row namedRead)
                            (fun row : BHist =>
                              PkgSig bundle namedRead pkg ∧ hsame row namedRead)
                            hsame ∧
                          UnaryHistory kindGateRead ∧ UnaryHistory matrixLedgerRead ∧
                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg
  intro kindUnary gateUnary matrixUnary ledgerUnary replayUnary localNameUnary
    kindGateCont matrixLedgerCont namedReadCont namedReadPkg
  have kindGateUnary : UnaryHistory kindGateRead :=
    unary_cont_closed kindUnary gateUnary kindGateCont
  have matrixLedgerUnary : UnaryHistory matrixLedgerRead :=
    unary_cont_closed matrixUnary ledgerUnary matrixLedgerCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary localNameUnary namedReadCont
  have sourceAtNamed : hsame namedRead namedRead ∧ UnaryHistory namedRead :=
    ⟨hsame_refl namedRead, namedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row kindGateRead ∨ hsame row matrixLedgerRead ∨ hsame row namedRead)
          (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceAtNamed
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨namedReadPkg, source.left⟩
  }
  exact ⟨cert, kindGateUnary, matrixLedgerUnary, namedReadUnary⟩

end BEDC.Derived.TypedGapSocketTaxonomyUp

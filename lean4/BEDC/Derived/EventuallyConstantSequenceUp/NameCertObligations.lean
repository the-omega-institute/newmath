import BEDC.Derived.EventuallyConstantSequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EventuallyConstantSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EventuallyConstantSequenceNamecertObligations [AskSetup] [PackageSetup]
    {stream tail constant readback limit sealRow _transport replay provenance localName endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream →
      UnaryHistory tail →
        UnaryHistory constant →
          UnaryHistory sealRow →
            UnaryHistory localName →
              Cont stream tail readback →
                Cont readback constant limit →
                  Cont limit sealRow replay →
                    Cont replay localName endpoint →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle endpoint pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row stream ∨ hsame row tail ∨
                                  hsame row constant ∨ hsame row readback ∨
                                    hsame row limit ∨ hsame row sealRow ∨
                                      hsame row endpoint)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle provenance pkg)
                              hsame ∧ UnaryHistory readback ∧ UnaryHistory limit ∧
                            UnaryHistory replay ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame SemanticNameCert
  intro streamUnary tailUnary constantUnary sealUnary localNameUnary
  intro readbackRoute limitRoute replayRoute endpointRoute provenancePkg endpointPkg
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamUnary tailUnary readbackRoute
  have limitUnary : UnaryHistory limit :=
    unary_cont_closed readbackUnary constantUnary limitRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed limitUnary sealUnary replayRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary localNameUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row tail ∨ hsame row constant ∨
            hsame row readback ∨ hsame row limit ∨ hsame row sealRow ∨
                hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg, provenancePkg⟩
  }
  exact ⟨cert, readbackUnary, limitUnary, replayUnary, endpointUnary⟩

end BEDC.Derived.EventuallyConstantSequenceUp

import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.WindowRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorScopedWindowConsumer [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName windowRead
      witnessRead sealRead ledgerRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont epsilon window windowRead →
        Cont windowRead stream witnessRead →
          Cont witnessRead readback sealRead →
            Cont sealRead realSeal ledgerRead →
              Cont ledgerRead localName consumerRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle consumerRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
                            hsame row readback ∨ hsame row realSeal ∨ hsame row windowRead ∨
                              hsame row witnessRead ∨ hsame row sealRead ∨
                                hsame row ledgerRead ∨ hsame row consumerRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont epsilon window windowRead ∧
                            Cont windowRead stream witnessRead ∧
                              Cont witnessRead readback sealRead ∧
                                Cont sealRead realSeal ledgerRead ∧
                                  Cont ledgerRead localName consumerRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle consumerRead pkg)
                        hsame ∧
                      UnaryHistory windowRead ∧ UnaryHistory witnessRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory ledgerRead ∧
                          UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: ChoiceFreeDiagonalSelectorCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier epsilonWindow windowStream witnessReadback sealReal ledgerLocal provenancePkg
    consumerPkg
  obtain ⟨epsilonUnary, windowUnary, streamUnary, readbackUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _storedWindowRoute,
    _storedReplayRoute, _storedProvenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary windowUnary epsilonWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowReadUnary streamUnary windowStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed witnessReadUnary readbackUnary witnessReadback
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sealReadUnary realSealUnary sealReal
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerReadUnary localNameUnary ledgerLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
              hsame row readback ∨ hsame row realSeal ∨ hsame row windowRead ∨
                hsame row witnessRead ∨ hsame row sealRead ∨ hsame row ledgerRead ∨
                  hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilon window windowRead ∧
              Cont windowRead stream witnessRead ∧ Cont witnessRead readback sealRead ∧
                Cont sealRead realSeal ledgerRead ∧ Cont ledgerRead localName consumerRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact
        ⟨source.right, epsilonWindow, windowStream, witnessReadback, sealReal,
          ledgerLocal, provenancePkg, consumerPkg⟩
  }
  exact
    ⟨cert, windowReadUnary, witnessReadUnary, sealReadUnary, ledgerReadUnary,
      consumerReadUnary⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp

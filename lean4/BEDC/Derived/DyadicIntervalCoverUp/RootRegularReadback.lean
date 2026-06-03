import BEDC.Derived.DyadicIntervalCoverUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootRegularReadback [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead readbackRead ledgerRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory Q →
        UnaryHistory M →
          UnaryHistory R →
            UnaryHistory V →
              UnaryHistory A →
                UnaryHistory N →
                  PkgSig bundle P pkg →
                    Cont W Q readbackRead →
                      Cont M R ledgerRead →
                        Cont readbackRead V sealRead →
                          Cont sealRead N namedRead →
                            PkgSig bundle namedRead pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row W ∨ hsame row Q ∨ hsame row M ∨
                                      hsame row R ∨ hsame row V ∨ hsame row A ∨
                                        hsame row N ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle namedRead pkg)
                                  hsame ∧
                                UnaryHistory readbackRead ∧ UnaryHistory ledgerRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro wUnary qUnary mUnary rUnary vUnary _aUnary nUnary provenancePkg
    readbackRoute ledgerRoute sealRoute nameRoute namedPkg
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed wUnary qUnary readbackRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed mUnary rUnary ledgerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary vUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row A ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, readbackUnary, ledgerUnary, sealUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp

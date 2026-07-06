import BEDC.Derived.TheorySelfClassifierUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheorySelfClassifier_ledger_obligation [AskSetup] [PackageSetup]
    {G E R P A L H C Q N classifierRead ledgerRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg ->
      Cont A L classifierRead ->
        Cont classifierRead H ledgerRead ->
          Cont ledgerRead C replayRead ->
            Cont replayRead N namedRead ->
              PkgSig bundle Q pkg ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row L \/ hsame row H \/ hsame row C \/ hsame row Q \/
                        hsame row N \/ hsame row classifierRead \/
                          hsame row ledgerRead \/ hsame row replayRead \/
                            hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row /\ Cont A L classifierRead /\
                        Cont classifierRead H ledgerRead /\
                          Cont ledgerRead C replayRead /\ Cont replayRead N namedRead /\
                            PkgSig bundle Q pkg /\ PkgSig bundle namedRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier classifierRoute ledgerRoute replayRoute namedRoute qPkg namedPkg
  obtain ⟨_gUnary, _eUnary, _rUnary, _pUnary, aUnary, lUnary, hUnary, cUnary,
    _qUnary, nUnary, _generatorEqualityRoute, _recursorPurityRoute,
    _classifierCarrierRoute, _provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed aUnary lUnary classifierRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed classifierUnary hUnary ledgerRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed ledgerUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  exact {
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, classifierRoute, ledgerRoute, replayRoute, namedRoute, qPkg,
          namedPkg⟩
  }

end BEDC.Derived.TheorySelfClassifierUp

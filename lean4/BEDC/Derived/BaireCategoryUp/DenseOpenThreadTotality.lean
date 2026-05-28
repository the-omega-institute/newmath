import BEDC.Derived.BaireCategoryUp.NameCertObligations

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_dense_open_thread_totality [AskSetup] [PackageSetup]
    {B M D O R T H C P N denseRead refinementRead threadRead terminalRead
      meagreRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg →
      Cont D O denseRead →
        Cont denseRead R refinementRead →
          Cont refinementRead T threadRead →
            Cont threadRead M terminalRead →
              Cont terminalRead N meagreRead →
                PkgSig bundle terminalRead pkg →
                  PkgSig bundle meagreRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row threadRead ∨ hsame row terminalRead ∨
                            hsame row meagreRead)
                        (fun row : BHist => UnaryHistory row)
                        (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
                        hsame ∧ UnaryHistory meagreRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute refinementRoute threadRoute terminalRoute meagreRoute _terminalPkg
    _meagrePkg
  obtain ⟨_baseUnary, metricUnary, denseUnary, openUnary, refinementUnary, threadUnary,
    _transportUnary, _replayUnary, _provenanceUnary, nameUnary, provenancePkg⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed denseUnary openUnary denseRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed denseReadUnary refinementUnary refinementRoute
  have threadReadUnary : UnaryHistory threadRead :=
    unary_cont_closed refinementReadUnary threadUnary threadRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed threadReadUnary metricUnary terminalRoute
  have meagreReadUnary : UnaryHistory meagreRead :=
    unary_cont_closed terminalReadUnary nameUnary meagreRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row threadRead ∨ hsame row terminalRead ∨ hsame row meagreRead)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro threadRead (Or.inl (hsame_refl threadRead))
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
        cases source with
        | inl sameThread =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameThread)
        | inr rest =>
            cases rest with
            | inl sameTerminal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal))
            | inr sameMeagre =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameMeagre))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameThread =>
          exact unary_transport threadReadUnary (hsame_symm sameThread)
      | inr rest =>
          cases rest with
          | inl sameTerminal =>
              exact unary_transport terminalReadUnary (hsame_symm sameTerminal)
          | inr sameMeagre =>
              exact unary_transport meagreReadUnary (hsame_symm sameMeagre)
    ledger_sound := by
      intro _row _source
      exact Or.inl provenancePkg
  }
  exact ⟨cert, meagreReadUnary⟩

end BEDC.Derived.BaireCategoryUp

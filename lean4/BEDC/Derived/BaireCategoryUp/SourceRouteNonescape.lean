import BEDC.Derived.BaireCategoryUp.NameCertObligations
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_source_route_nonescape [AskSetup] [PackageSetup]
    {B M D O R T H C P N sourceRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont B M sourceRead ->
        Cont sourceRead T terminalRead ->
          PkgSig bundle terminalRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row sourceRead ∨ hsame row terminalRead ∨ hsame row P)
                (fun row : BHist => UnaryHistory row)
                (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory terminalRead ∧ Cont B M sourceRead ∧
                Cont sourceRead T terminalRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute terminalRoute terminalPkg
  obtain ⟨prefixUnary, metricUnary, _denseUnary, _openUnary, _refinementUnary,
    threadUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed prefixUnary metricUnary sourceRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sourceReadUnary threadUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row terminalRead ∨ hsame row P)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead (Or.inl (hsame_refl sourceRead))
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
        | inl sameSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
        | inr rest =>
            cases rest with
            | inl sameTerminal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal))
            | inr sameProvenance =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameProvenance))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameSource =>
          exact unary_transport sourceReadUnary (hsame_symm sameSource)
      | inr rest =>
          cases rest with
          | inl sameTerminal =>
              exact unary_transport terminalReadUnary (hsame_symm sameTerminal)
          | inr sameProvenance =>
              exact unary_transport provenanceUnary (hsame_symm sameProvenance)
    ledger_sound := by
      intro _row source
      cases source with
      | inl _sameSource =>
          exact Or.inl provenancePkg
      | inr rest =>
          cases rest with
          | inl _sameTerminal =>
              exact Or.inl provenancePkg
          | inr _sameProvenance =>
              exact Or.inl provenancePkg
  }
  exact
    ⟨cert, sourceReadUnary, terminalReadUnary, sourceRoute, terminalRoute, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.BaireCategoryUp

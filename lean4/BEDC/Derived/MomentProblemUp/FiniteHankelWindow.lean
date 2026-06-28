import BEDC.Derived.MomentProblemUp.TasteGate

namespace BEDC.Derived.MomentProblemUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace FiniteHankelWindow

theorem MomentProblemCarrier_finite_hankel_window [AskSetup] [PackageSetup]
    {rat real hankel0 hankel1 window positivity distribution transport replay provenance
      localName hankelWindow positivityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MomentProblemCarrier rat real hankel0 hankel1 window positivity distribution transport
        replay provenance localName bundle pkg ->
      Cont rat real hankelWindow ->
        Cont hankelWindow hankel0 positivityRead ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row positivityRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row rat ∨ hsame row real ∨ hsame row hankel0 ∨
                    hsame row hankel1 ∨ hsame row window ∨ hsame row positivity ∨
                      hsame row positivityRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont rat real hankelWindow ∧
                    Cont hankelWindow hankel0 positivityRead ∧
                      PkgSig bundle provenance pkg)
                hsame ∧ UnaryHistory hankelWindow ∧ UnaryHistory positivityRead := by
  -- BEDC touchpoint anchor: MomentProblemCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier ratReal hankelRoute provenancePkg
  obtain ⟨ratUnary, realUnary, hankel0Unary, _hankel1Unary, _windowUnary,
    _positivityUnary, _distributionUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierRatReal, _carrierHankelWindow, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have hankelWindowUnary : UnaryHistory hankelWindow :=
    unary_cont_closed ratUnary realUnary ratReal
  have positivityReadUnary : UnaryHistory positivityRead :=
    unary_cont_closed hankelWindowUnary hankel0Unary hankelRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row positivityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row rat ∨ hsame row real ∨ hsame row hankel0 ∨
              hsame row hankel1 ∨ hsame row window ∨ hsame row positivity ∨
                hsame row positivityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont rat real hankelWindow ∧
              Cont hankelWindow hankel0 positivityRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro positivityRead ⟨hsame_refl positivityRead, positivityReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, ratReal, hankelRoute, provenancePkg⟩
  }
  exact ⟨cert, hankelWindowUnary, positivityReadUnary⟩

end FiniteHankelWindow

end BEDC.Derived.MomentProblemUp

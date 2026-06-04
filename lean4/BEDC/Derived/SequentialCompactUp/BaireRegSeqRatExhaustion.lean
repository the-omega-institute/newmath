import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactBaireRegSeqRatExhaustion [AskSetup] [PackageSetup]
    {K B S W R E H C P N baireRead windowRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont K B baireRead ->
        Cont baireRead W windowRead ->
          Cont windowRead R regularRead ->
            PkgSig bundle regularRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                      hsame row baireRead ∨ hsame row windowRead ∨
                        hsame row regularRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K B baireRead ∧
                      Cont baireRead W windowRead ∧ Cont windowRead R regularRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle regularRead pkg)
                  hsame ∧ UnaryHistory baireRead ∧ UnaryHistory windowRead ∧
                UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier baireRoute windowRoute regularRoute regularPkg
  obtain ⟨kUnary, _bUnary, _sUnary, wUnary, rUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed kUnary _bUnary baireRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed baireUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row baireRead ∨ hsame row windowRead ∨ hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K B baireRead ∧ Cont baireRead W windowRead ∧
              Cont windowRead R regularRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle regularRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regularRead ⟨hsame_refl regularRead, regularUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, baireRoute, windowRoute, regularRoute, provenancePkg, regularPkg⟩
  }
  exact ⟨cert, baireUnary, windowUnary, regularUnary⟩

end BEDC.Derived.SequentialCompactUp

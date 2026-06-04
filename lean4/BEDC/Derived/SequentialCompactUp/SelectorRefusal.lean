import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactSelectorRefusal [AskSetup] [PackageSetup]
    {K B S W R E H C P N selectorRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont S W selectorRead ->
        Cont selectorRead R refusalRead ->
          PkgSig bundle refusalRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row refusalRead)
                (fun row : BHist =>
                  hsame row refusalRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle refusalRead pkg)
                hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier selectorRoute refusalRoute refusalPkg
  obtain ⟨_kUnary, _bUnary, sUnary, wUnary, rUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed sUnary wUnary selectorRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed selectorUnary rUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, provenancePkg, refusalPkg⟩
  }
  exact ⟨cert, selectorUnary, refusalUnary⟩

end BEDC.Derived.SequentialCompactUp

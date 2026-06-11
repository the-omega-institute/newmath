import BEDC.Derived.LawlessSequenceUp.ChoiceFreeCarrierObligation

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceRealBoundaryNonescape [AskSetup] [PackageSetup]
    {W B I H C P N digitRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier W B I H C P N bundle pkg ->
      Cont W B digitRead ->
        Cont digitRead N boundaryRead ->
          PkgSig bundle boundaryRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row digitRead ∨ hsame row boundaryRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W B digitRead ∧ Cont digitRead N boundaryRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg)
                hsame ∧ UnaryHistory digitRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrierRows digitRoute boundaryRoute boundaryPkg
  obtain ⟨wUnary, bUnary, _iUnary, _hUnary, _cUnary, pUnary, nUnary, provenancePkg,
    _localNamePkg⟩ := carrierRows
  have _provenanceUnary : UnaryHistory P := pUnary
  have digitUnary : UnaryHistory digitRead :=
    unary_cont_closed wUnary bUnary digitRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed digitUnary nUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row B ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row digitRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W B digitRead ∧ Cont digitRead N boundaryRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, digitRoute, boundaryRoute, provenancePkg, boundaryPkg⟩
  }
  exact ⟨cert, digitUnary, boundaryUnary⟩

end BEDC.Derived.LawlessSequenceUp

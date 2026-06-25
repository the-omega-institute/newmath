import BEDC.Derived.BishopChainConnectedUp.TasteGate

namespace BEDC.Derived.BishopChainConnectedUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopChainConnectedCarrier_interval_handoff [AskSetup] [PackageSetup]
    {I A Z D J W R Q H C P N chainRead sealRead intervalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopChainConnectedCarrier I A Z D J W R Q H C P N bundle pkg ->
      Cont Z D chainRead ->
        Cont chainRead Q sealRead ->
          Cont sealRead N intervalRead ->
            PkgSig bundle intervalRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row intervalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row A ∨ hsame row Z ∨ hsame row D ∨
                      hsame row J ∨ hsame row W ∨ hsame row R ∨ hsame row Q ∨
                        hsame row sealRead ∨ hsame row intervalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z D chainRead ∧ Cont chainRead Q sealRead ∧
                      Cont sealRead N intervalRead ∧ PkgSig bundle intervalRead pkg)
                  hsame ∧
                UnaryHistory intervalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier chainRoute sealRoute intervalRoute intervalPkg
  obtain ⟨_iUnary, _aUnary, zUnary, dUnary, _jUnary, _wUnary, _rUnary, qUnary,
    _hUnary, _cUnary, _pUnary, nUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed zUnary dUnary chainRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed chainReadUnary qUnary sealRoute
  have intervalReadUnary : UnaryHistory intervalRead :=
    unary_cont_closed sealReadUnary nUnary intervalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row intervalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row A ∨ hsame row Z ∨ hsame row D ∨ hsame row J ∨
              hsame row W ∨ hsame row R ∨ hsame row Q ∨ hsame row sealRead ∨
                hsame row intervalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z D chainRead ∧ Cont chainRead Q sealRead ∧
              Cont sealRead N intervalRead ∧ PkgSig bundle intervalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro intervalRead ⟨hsame_refl intervalRead, intervalReadUnary⟩
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
      exact ⟨source.right, chainRoute, sealRoute, intervalRoute, intervalPkg⟩
  }
  exact ⟨cert, intervalReadUnary⟩

end BEDC.Derived.BishopChainConnectedUp

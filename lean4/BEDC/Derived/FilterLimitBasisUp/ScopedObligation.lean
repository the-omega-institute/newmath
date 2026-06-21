import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisScopedObligation [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N completionRead limitRead sealRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg ->
      Cont Q F completionRead ->
        Cont L W limitRead ->
          Cont R E sealRead ->
            Cont sealRead N scopedRead ->
              PkgSig bundle scopedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
                        hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row N ∨
                          hsame row scopedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont Q F completionRead ∧
                        Cont L W limitRead ∧ Cont R E sealRead ∧
                          Cont sealRead N scopedRead ∧ PkgSig bundle scopedRead pkg)
                    hsame ∧
                  UnaryHistory completionRead ∧ UnaryHistory limitRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute limitRoute sealRoute scopedRoute scopedPkg
  obtain
    ⟨qUnary, fUnary, lUnary, wUnary, rUnary, _dUnary, eUnary, _hUnary, _cUnary,
      _pUnary, nUnary, _sameHN, _carrierPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed qUnary fUnary completionRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed lUnary wUnary limitRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed sealUnary nUnary scopedRoute
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row N ∨
                hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F completionRead ∧ Cont L W limitRead ∧
              Cont R E sealRead ∧ Cont sealRead N scopedRead ∧
                PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceScoped
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionRoute, limitRoute, sealRoute, scopedRoute, scopedPkg⟩
  }
  exact ⟨cert, completionUnary, limitUnary, sealUnary, scopedUnary⟩

end BEDC.Derived.FilterLimitBasisUp

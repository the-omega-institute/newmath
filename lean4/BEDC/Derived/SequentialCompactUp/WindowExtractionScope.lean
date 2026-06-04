import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactWindowExtractionScope [AskSetup] [PackageSetup]
    {K B S W R E H C P N baireRead selectedRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont K B baireRead →
        Cont baireRead W selectedRead →
          Cont selectedRead R regularRead →
            PkgSig bundle regularRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                      hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row baireRead ∨ hsame row selectedRead ∨
                          hsame row regularRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K B baireRead ∧
                      Cont baireRead W selectedRead ∧ Cont selectedRead R regularRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle regularRead pkg)
                  hsame ∧ UnaryHistory baireRead ∧ UnaryHistory selectedRead ∧
                UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier baireRoute selectedRoute regularRoute regularPkg
  obtain ⟨kUnary, bUnary, _sUnary, wUnary, rUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed kUnary bUnary baireRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed baireUnary wUnary selectedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed selectedUnary rUnary regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row baireRead ∨ hsame row selectedRead ∨ hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K B baireRead ∧ Cont baireRead W selectedRead ∧
              Cont selectedRead R regularRead ∧ PkgSig bundle P pkg ∧
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, baireRoute, selectedRoute, regularRoute, provenancePkg, regularPkg⟩
  }
  exact ⟨cert, baireUnary, selectedUnary, regularUnary⟩

end BEDC.Derived.SequentialCompactUp

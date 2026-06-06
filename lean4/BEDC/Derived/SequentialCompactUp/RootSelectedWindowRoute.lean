import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRootSelectedWindowRoute [AskSetup] [PackageSetup]
    {K B S W R E H C P N baireRead streamRead selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont K B baireRead →
        Cont baireRead S streamRead →
          Cont streamRead W selectedRead →
            PkgSig bundle selectedRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row selectedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                      hsame row baireRead ∨ hsame row streamRead ∨
                        hsame row selectedRead)
                  (fun row : BHist =>
                    hsame row selectedRead ∧ Cont K B baireRead ∧
                      Cont baireRead S streamRead ∧ Cont streamRead W selectedRead ∧
                        PkgSig bundle selectedRead pkg)
                  hsame ∧ UnaryHistory baireRead ∧ UnaryHistory streamRead ∧
                UnaryHistory selectedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier baireRoute streamRoute selectedRoute selectedPkg
  obtain ⟨kUnary, bUnary, sUnary, wUnary, _rUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed kUnary bUnary baireRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed baireUnary sUnary streamRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed streamUnary wUnary selectedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row selectedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
              hsame row baireRead ∨ hsame row streamRead ∨ hsame row selectedRead)
          (fun row : BHist =>
            hsame row selectedRead ∧ Cont K B baireRead ∧
              Cont baireRead S streamRead ∧ Cont streamRead W selectedRead ∧
                PkgSig bundle selectedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectedRead
        ⟨hsame_refl selectedRead, selectedUnary, selectedPkg⟩
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, baireRoute, streamRoute, selectedRoute, selectedPkg⟩
  }
  exact ⟨cert, baireUnary, streamUnary, selectedUnary⟩

end BEDC.Derived.SequentialCompactUp

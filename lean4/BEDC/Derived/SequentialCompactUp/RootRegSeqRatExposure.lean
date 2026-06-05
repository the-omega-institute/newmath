import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRootRegSeqRatExposure [AskSetup] [PackageSetup]
    {K B S W R E H C P N selectedWindow regularTail exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont S W selectedWindow →
        Cont selectedWindow R regularTail →
          Cont regularTail N exportedRead →
            PkgSig bundle exportedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row N ∨
                      hsame row selectedWindow ∨ hsame row regularTail ∨
                        hsame row exportedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S W selectedWindow ∧
                      Cont selectedWindow R regularTail ∧
                        Cont regularTail N exportedRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle exportedRead pkg)
                  hsame ∧ UnaryHistory selectedWindow ∧ UnaryHistory regularTail ∧
                UnaryHistory exportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectedRoute regularRoute exportedRoute exportedPkg
  obtain ⟨_kUnary, _bUnary, sUnary, wUnary, rUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed sUnary wUnary selectedRoute
  have regularUnary : UnaryHistory regularTail :=
    unary_cont_closed selectedUnary rUnary regularRoute
  have exportedUnary : UnaryHistory exportedRead :=
    unary_cont_closed regularUnary nUnary exportedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row N ∨
              hsame row selectedWindow ∨ hsame row regularTail ∨
                hsame row exportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W selectedWindow ∧
              Cont selectedWindow R regularTail ∧ Cont regularTail N exportedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle exportedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportedRead
        ⟨hsame_refl exportedRead, exportedUnary⟩
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
      exact
        ⟨sourceRow.right, selectedRoute, regularRoute, exportedRoute, provenancePkg,
          exportedPkg⟩
  }
  exact ⟨cert, selectedUnary, regularUnary, exportedUnary⟩

end BEDC.Derived.SequentialCompactUp

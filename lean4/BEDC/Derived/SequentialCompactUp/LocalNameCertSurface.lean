import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactCarrier_local_namecert_surface [AskSetup] [PackageSetup]
    {K B S W R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      PkgSig bundle N pkg ->
        SemanticNameCert
            (fun row : BHist => hsame row N ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                  hsame row P ∨ hsame row N)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
            hsame ∧
          UnaryHistory N := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier localPkg
  obtain ⟨_kUnary, _bUnary, _sUnary, _wUnary, _rUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, nUnary, _compactBaireStream, _streamWindowRegular,
      _regularSealTransport, _transportReplayProvenance, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      exact ⟨source.right, provenancePkg, localPkg⟩
  }
  exact ⟨cert, nUnary⟩

end BEDC.Derived.SequentialCompactUp

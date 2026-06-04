import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactCylinderMonotoneWindow [AskSetup] [PackageSetup]
    {K B S W R E H C P N cylinderRead selectedRead monotoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont B S cylinderRead -> Cont cylinderRead W selectedRead ->
        Cont selectedRead H monotoneRead -> PkgSig bundle monotoneRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row monotoneRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row H ∨ hsame row C ∨
                hsame row monotoneRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont B S cylinderRead ∧
                Cont cylinderRead W selectedRead ∧ Cont selectedRead H monotoneRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle monotoneRead pkg)
            hsame ∧ UnaryHistory cylinderRead ∧ UnaryHistory selectedRead ∧
              UnaryHistory monotoneRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier cylinderRoute selectedRoute monotoneRoute monotonePkg
  obtain ⟨_kUnary, bUnary, sUnary, wUnary, _rUnary, _eUnary, hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have cylinderUnary : UnaryHistory cylinderRead :=
    unary_cont_closed bUnary sUnary cylinderRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed cylinderUnary wUnary selectedRoute
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed selectedUnary hUnary monotoneRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row monotoneRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row H ∨ hsame row C ∨
            hsame row monotoneRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont B S cylinderRead ∧ Cont cylinderRead W selectedRead ∧
            Cont selectedRead H monotoneRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle monotoneRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro monotoneRead ⟨hsame_refl monotoneRead, monotoneUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cylinderRoute, selectedRoute, monotoneRoute, provenancePkg,
          monotonePkg⟩
  }
  exact ⟨cert, cylinderUnary, selectedUnary, monotoneUnary⟩

end BEDC.Derived.SequentialCompactUp

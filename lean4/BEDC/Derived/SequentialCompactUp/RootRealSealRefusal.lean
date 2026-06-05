import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRootRealSealRefusal [AskSetup] [PackageSetup]
    {K B S W R E H C P N windowRead regularRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont B S windowRead ->
        Cont windowRead W regularRead ->
          Cont regularRead R sealRead ->
            Cont sealRead E namedRead ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                        hsame row R ∨ hsame row E ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont B S windowRead ∧
                        Cont windowRead W regularRead ∧ Cont regularRead R sealRead ∧
                          Cont sealRead E namedRead ∧ PkgSig bundle namedRead pkg)
                    hsame ∧ UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute regularRoute sealRoute namedRoute namedPkg
  obtain ⟨_kUnary, bUnary, sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bUnary sUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary wUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary rUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary eUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B S windowRead ∧ Cont windowRead W regularRead ∧
              Cont regularRead R sealRead ∧ Cont sealRead E namedRead ∧
                PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        ⟨sourceRow.right, windowRoute, regularRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, windowUnary, regularUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialCompactUp

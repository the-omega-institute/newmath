import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactCompactMetricRootSurface [AskSetup] [PackageSetup]
    {K B S W R E H C P N compactRead windowRead regularRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont K B compactRead →
        Cont compactRead W windowRead →
          Cont windowRead R regularRead →
            Cont regularRead E sealRead →
              Cont sealRead N namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row B ∨ hsame row W ∨ hsame row R ∨
                          hsame row E ∨ hsame row N ∨ hsame row compactRead ∨
                            hsame row windowRead ∨ hsame row regularRead ∨
                              hsame row sealRead ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K B compactRead ∧
                          Cont compactRead W windowRead ∧
                            Cont windowRead R regularRead ∧
                              Cont regularRead E sealRead ∧ Cont sealRead N namedRead ∧
                                PkgSig bundle namedRead pkg)
                      hsame ∧ UnaryHistory compactRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute windowRoute regularRoute sealRoute namedRoute namedPkg
  obtain ⟨kUnary, bUnary, _sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed kUnary bUnary compactRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed compactUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row N ∨ hsame row compactRead ∨ hsame row windowRead ∨
                hsame row regularRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K B compactRead ∧ Cont compactRead W windowRead ∧
              Cont windowRead R regularRead ∧ Cont regularRead E sealRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead
        ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, windowRoute, regularRoute, sealRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, compactUnary, windowUnary, regularUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialCompactUp

import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRootObligationSurface [AskSetup] [PackageSetup]
    {K B S W R E H C P N baireRead streamRead selectedRead regularRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont K B baireRead →
        Cont baireRead S streamRead →
          Cont streamRead W selectedRead →
            Cont selectedRead R regularRead →
              Cont regularRead E sealRead →
                Cont H N namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                            hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row N ∨
                              hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont K B baireRead ∧
                            Cont baireRead S streamRead ∧
                              Cont streamRead W selectedRead ∧
                                Cont selectedRead R regularRead ∧
                                  Cont regularRead E sealRead ∧ Cont H N namedRead ∧
                                    PkgSig bundle namedRead pkg)
                        hsame ∧ UnaryHistory baireRead ∧ UnaryHistory streamRead ∧
                      UnaryHistory selectedRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier baireRoute streamRoute selectedRoute regularRoute sealRoute namedRoute
    namedPkg
  obtain ⟨unaryK, unaryB, unaryS, unaryW, unaryR, unaryE, unaryH, _unaryC, _unaryP,
    unaryN, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed unaryK unaryB baireRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed baireUnary unaryS streamRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed streamUnary unaryW selectedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed selectedUnary unaryR regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary unaryE sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed unaryH unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K B baireRead ∧ Cont baireRead S streamRead ∧
              Cont streamRead W selectedRead ∧ Cont selectedRead R regularRead ∧
                Cont regularRead E sealRead ∧ Cont H N namedRead ∧
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
      exact
        ⟨source.right, baireRoute, streamRoute, selectedRoute, regularRoute, sealRoute,
          namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, baireUnary, streamUnary, selectedUnary, regularUnary, sealUnary,
      namedUnary⟩

end BEDC.Derived.SequentialCompactUp

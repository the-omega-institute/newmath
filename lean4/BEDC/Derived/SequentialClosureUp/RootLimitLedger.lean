import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureRootLimitLedger [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N limitRead windowRead rationalRead sealRead transported
      replayed named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg →
      Cont L U limitRead →
        Cont limitRead W windowRead →
          Cont windowRead R rationalRead →
            Cont rationalRead A sealRead →
              Cont sealRead H transported →
                Cont transported C replayed →
                  Cont replayed N named →
                    PkgSig bundle named pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row named ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
                              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row N ∨
                                hsame row named)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont L U limitRead ∧
                              Cont limitRead W windowRead ∧
                                Cont windowRead R rationalRead ∧
                                  Cont rationalRead A sealRead ∧
                                    Cont sealRead H transported ∧
                                      Cont transported C replayed ∧
                                        PkgSig bundle named pkg)
                          hsame ∧ UnaryHistory limitRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory rationalRead ∧ UnaryHistory sealRead ∧
                          UnaryHistory transported ∧ UnaryHistory replayed ∧
                            UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier limitRoute windowRoute rationalRoute sealRoute transportedRoute replayedRoute
    namedRoute namedPkg
  obtain ⟨_topologyUnary, _metricUnary, _sourceUnary, _sequenceUnary, limitUnaryBase,
    testUnary, windowUnaryBase, rationalUnaryBase, sealUnaryBase, transportUnaryBase,
    continuationUnary, _provenanceUnary, nameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnaryBase testUnary limitRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed limitUnary windowUnaryBase windowRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed windowUnary rationalUnaryBase rationalRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalUnary sealUnaryBase sealRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sealUnary transportUnaryBase transportedRoute
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary continuationUnary replayedRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed replayedUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row N ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U limitRead ∧ Cont limitRead W windowRead ∧
              Cont windowRead R rationalRead ∧ Cont rationalRead A sealRead ∧
                Cont sealRead H transported ∧ Cont transported C replayed ∧
                  PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        ⟨source.right, limitRoute, windowRoute, rationalRoute, sealRoute,
          transportedRoute, replayedRoute, namedPkg⟩
  }
  exact
    ⟨cert, limitUnary, windowUnary, rationalUnary, sealUnary, transportedUnary,
      replayedUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp

import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureRootTopologyTransport [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N topologyRead sourceRead limitRead transported replayed
      named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg →
      Cont T M topologyRead →
        Cont S Q sourceRead →
          Cont L U limitRead →
            Cont limitRead H transported →
              Cont transported C replayed →
                Cont replayed P named →
                  PkgSig bundle named pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row named ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
                            hsame row L ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                              hsame row P ∨ hsame row named)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont T M topologyRead ∧
                            Cont S Q sourceRead ∧ Cont L U limitRead ∧
                              Cont limitRead H transported ∧
                                Cont transported C replayed ∧ PkgSig bundle named pkg)
                        hsame ∧ UnaryHistory topologyRead ∧ UnaryHistory sourceRead ∧
                      UnaryHistory limitRead ∧ UnaryHistory transported ∧
                        UnaryHistory replayed ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier topologyRoute sourceRoute limitRoute transportedRoute replayedRoute namedRoute
    namedPkg
  obtain ⟨topologyUnaryBase, metricUnaryBase, sourceUnaryBase, sequenceUnaryBase,
    limitUnaryBase, testUnary, _windowUnary, _rationalUnary, _sealUnary, transportUnaryBase,
    continuationUnary, provenanceUnary, _nameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have topologyUnary : UnaryHistory topologyRead :=
    unary_cont_closed topologyUnaryBase metricUnaryBase topologyRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnaryBase sequenceUnaryBase sourceRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnaryBase testUnary limitRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed limitUnary transportUnaryBase transportedRoute
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary continuationUnary replayedRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed replayedUnary provenanceUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨ hsame row L ∨
              hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T M topologyRead ∧ Cont S Q sourceRead ∧
              Cont L U limitRead ∧ Cont limitRead H transported ∧
                Cont transported C replayed ∧ PkgSig bundle named pkg)
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, topologyRoute, sourceRoute, limitRoute, transportedRoute,
          replayedRoute, namedPkg⟩
  }
  exact
    ⟨cert, topologyUnary, sourceUnary, limitUnary, transportedUnary, replayedUnary,
      namedUnary⟩

end BEDC.Derived.SequentialClosureUp

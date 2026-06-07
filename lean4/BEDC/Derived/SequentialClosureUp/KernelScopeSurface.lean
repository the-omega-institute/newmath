import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureKernelScopeSurface [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N topologyRead sourceRead limitRead windowRead sealRead
      named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg ->
      Cont T M topologyRead ->
        Cont topologyRead S sourceRead ->
          Cont sourceRead L limitRead ->
            Cont limitRead W windowRead ->
              Cont windowRead A sealRead ->
                Cont sealRead N named ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row named ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row L ∨
                              hsame row W ∨ hsame row A ∨ hsame row named)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory topologyRead ∧ UnaryHistory sourceRead ∧
                          UnaryHistory limitRead ∧ UnaryHistory windowRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: SequentialClosureCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier topologyRoute sourceRoute limitRoute windowRoute sealRoute namedRoute
    provenancePkg namePkg
  obtain ⟨topologyUnary, metricUnary, sourceUnary, _sequenceUnary, limitUnaryBase,
    _testUnary, windowUnaryBase, _regSeqUnary, sealUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, nUnary, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have topologyReadUnary : UnaryHistory topologyRead :=
    unary_cont_closed topologyUnary metricUnary topologyRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed topologyReadUnary sourceUnary sourceRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed sourceReadUnary limitUnaryBase limitRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed limitReadUnary windowUnaryBase windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnaryBase sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealReadUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row L ∨ hsame row W ∨
              hsame row A ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, topologyReadUnary, sourceReadUnary, limitReadUnary, windowReadUnary,
      sealReadUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp

import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureTopologySequenceFilterHandoff [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N neighbourhoodRead windowRead regSeqRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg →
      Cont T U neighbourhoodRead →
        Cont neighbourhoodRead W windowRead →
          Cont windowRead R regSeqRead →
            Cont regSeqRead A sealRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row T ∨ hsame row S ∨ hsame row Q ∨ hsame row W ∨
                          hsame row R ∨ hsame row A ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont T U neighbourhoodRead ∧
                          Cont neighbourhoodRead W windowRead ∧
                            Cont windowRead R regSeqRead ∧
                              Cont regSeqRead A sealRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                      hsame ∧ UnaryHistory neighbourhoodRead ∧
                    UnaryHistory windowRead ∧ UnaryHistory regSeqRead ∧
                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: SequentialClosureCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier neighbourhoodRoute windowRoute regSeqRoute sealRoute pPkg nPkg
  obtain ⟨topologyUnary, _metricUnary, _subsetUnary, _sequenceUnary, _limitUnary,
    testUnary, windowUnaryBase, regSeqUnaryBase, sealUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, _nameUnary, _provenancePkg, _namePkg⟩ :=
    carrier
  have neighbourhoodUnary : UnaryHistory neighbourhoodRead :=
    unary_cont_closed topologyUnary testUnary neighbourhoodRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed neighbourhoodUnary windowUnaryBase windowRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed windowUnary regSeqUnaryBase regSeqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regSeqUnary sealUnaryBase sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row Q ∨ hsame row W ∨ hsame row R ∨
              hsame row A ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T U neighbourhoodRead ∧
              Cont neighbourhoodRead W windowRead ∧ Cont windowRead R regSeqRead ∧
                Cont regSeqRead A sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, neighbourhoodRoute, windowRoute, regSeqRoute, sealRoute, pPkg,
          nPkg⟩
  }
  exact ⟨cert, neighbourhoodUnary, windowUnary, regSeqUnary, sealUnary⟩

end BEDC.Derived.SequentialClosureUp

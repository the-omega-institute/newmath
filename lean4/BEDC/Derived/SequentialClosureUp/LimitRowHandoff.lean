import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureLimitRowHandoff [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N limitRead windowRead regSeqRead sealRead named :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg ->
      Cont L U limitRead ->
        Cont limitRead W windowRead ->
          Cont windowRead R regSeqRead ->
            Cont regSeqRead A sealRead ->
              Cont sealRead N named ->
                PkgSig bundle named pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row named ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
                          hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
                            hsame row A ∨ hsame row named)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L U limitRead ∧
                          Cont limitRead W windowRead ∧
                            Cont windowRead R regSeqRead ∧
                              Cont regSeqRead A sealRead ∧ PkgSig bundle named pkg)
                      hsame ∧ UnaryHistory limitRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regSeqRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier limitRoute windowRoute regSeqRoute sealRoute namedRoute namedPkg
  obtain ⟨_topologyUnary, _metricUnary, _sourceUnary, _sequenceUnary, limitUnaryBase,
    testUnary, windowUnaryBase, regSeqUnaryBase, sealUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, nameUnary, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnaryBase testUnary limitRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed limitUnary windowUnaryBase windowRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed windowUnary regSeqUnaryBase regSeqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regSeqUnary sealUnaryBase sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨ hsame row L ∨
              hsame row U ∨ hsame row W ∨ hsame row R ∨ hsame row A ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U limitRead ∧ Cont limitRead W windowRead ∧
              Cont windowRead R regSeqRead ∧ Cont regSeqRead A sealRead ∧
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, limitRoute, windowRoute, regSeqRoute, sealRoute, namedPkg⟩
  }
  exact ⟨cert, limitUnary, windowUnary, regSeqUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp

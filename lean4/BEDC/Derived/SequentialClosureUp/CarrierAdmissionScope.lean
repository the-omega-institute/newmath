import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureCarrierAdmissionScope [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N admittedRead windowRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg ->
      Cont S U admittedRead ->
        Cont admittedRead W windowRead ->
          Cont windowRead A sealRead ->
            Cont sealRead N named ->
              PkgSig bundle named pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row named ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row U ∨ hsame row W ∨ hsame row A ∨
                        hsame row named)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S U admittedRead ∧
                        Cont admittedRead W windowRead ∧ Cont windowRead A sealRead ∧
                          PkgSig bundle named pkg)
                    hsame ∧ UnaryHistory admittedRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: SequentialClosureCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier admittedRoute windowRoute sealRoute namedRoute namedPkg
  obtain ⟨_topologyUnary, _metricUnary, sourceUnary, _sequenceUnary, _limitUnary,
    testUnary, windowUnaryBase, _regSeqUnary, sealUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, nUnary, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have admittedUnary : UnaryHistory admittedRead :=
    unary_cont_closed sourceUnary testUnary admittedRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed admittedUnary windowUnaryBase windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary sealUnaryBase sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row W ∨ hsame row A ∨
              hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U admittedRead ∧
              Cont admittedRead W windowRead ∧ Cont windowRead A sealRead ∧
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, admittedRoute, windowRoute, sealRoute, namedPkg⟩
  }
  exact ⟨cert, admittedUnary, windowUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp

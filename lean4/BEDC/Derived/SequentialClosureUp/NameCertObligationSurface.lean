import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureNameCert_obligation_surface [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N requestRead windowRead handoffRead sealRead named :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg ->
      Cont T Q requestRead ->
        Cont requestRead U windowRead ->
          Cont windowRead W handoffRead ->
            Cont handoffRead A sealRead ->
              Cont sealRead N named ->
                PkgSig bundle named pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                      (fun row : BHist =>
                        hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
                          hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
                            hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                              hsame row N ∨ hsame row requestRead ∨
                                hsame row windowRead ∨ hsame row handoffRead ∨
                                  hsame row sealRead ∨ hsame row named)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont T Q requestRead ∧
                          Cont requestRead U windowRead ∧
                            Cont windowRead W handoffRead ∧
                              Cont handoffRead A sealRead ∧ Cont sealRead N named ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory requestRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory handoffRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier requestRoute windowRoute handoffRoute sealRoute namedRoute namedPkg
  obtain ⟨topologyUnary, _metricUnary, _subsetUnary, sequenceUnary, _limitUnary,
    testUnary, windowUnaryBase, _handoffUnaryBase, sealUnaryBase, _transportUnary,
    _continuationUnary, pUnary, nUnary, pPkg, nPkg⟩ := carrier
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed topologyUnary sequenceUnary requestRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed requestUnary testUnary windowRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed windowUnary windowUnaryBase handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary sealUnaryBase sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary nUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row named ∧ UnaryHistory row ∧
        PkgSig bundle row pkg) named := by
    exact ⟨hsame_refl named, namedUnary, namedPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
              hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row R ∨
                hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row requestRead ∨ hsame row windowRead ∨
                    hsame row handoffRead ∨ hsame row sealRead ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T Q requestRead ∧
              Cont requestRead U windowRead ∧ Cont windowRead W handoffRead ∧
                Cont handoffRead A sealRead ∧ Cont sealRead N named ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named sourceNamed
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
        cases sameRows
        exact source
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr source.left))))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right.left, requestRoute, windowRoute, handoffRoute, sealRoute,
          namedRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, requestUnary, windowUnary, handoffUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialClosureUp

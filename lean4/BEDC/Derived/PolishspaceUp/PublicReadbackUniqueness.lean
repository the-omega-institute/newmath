import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpacePublicReadbackUniqueness [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead densityRead windowRead sealRead leftRead
      rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont M K completionRead ->
        Cont M D densityRead ->
          Cont completionRead densityRead windowRead ->
            Cont windowRead W sealRead ->
              Cont sealRead R leftRead ->
                Cont sealRead R rightRead ->
                  hsame leftRead rightRead ->
                    PkgSig bundle G pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row leftRead ∨ hsame row rightRead) ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                                hsame row W ∨ hsame row sealRead ∨ hsame row leftRead ∨
                                  hsame row rightRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont completionRead densityRead windowRead ∧
                                Cont windowRead W sealRead ∧ Cont sealRead R leftRead ∧
                                  Cont sealRead R rightRead ∧ PkgSig bundle G pkg ∧
                                    PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory leftRead ∧ UnaryHistory rightRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier completionRoute densityRoute windowRoute sealRoute leftRoute rightRoute
    sameReads provenancePkg localNamePkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed MUnary DUnary densityRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed completionUnary densityUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary WUnary sealRoute
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed sealUnary RUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed sealUnary RUnary rightRoute
  have sourceLeft :
      (fun row : BHist => (hsame row leftRead ∨ hsame row rightRead) ∧ UnaryHistory row)
        leftRead := by
    exact ⟨Or.inl (hsame_refl leftRead), leftUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row leftRead ∨ hsame row rightRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row W ∨
              hsame row sealRead ∨ hsame row leftRead ∨ hsame row rightRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completionRead densityRead windowRead ∧
              Cont windowRead W sealRead ∧ Cont sealRead R leftRead ∧
                Cont sealRead R rightRead ∧ PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro leftRead sourceLeft
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
        have sourceRoute :
            hsame _other leftRead ∨ hsame _other rightRead := by
          cases source.left with
          | inl leftSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) leftSame)
          | inr rightSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) rightSame)
        exact ⟨sourceRoute, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl leftSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl leftSame))))))
      | inr rightSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rightSame))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, sealRoute, leftRoute, rightRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary⟩

end BEDC.Derived.PolishSpaceUp

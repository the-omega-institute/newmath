import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpacePublicCompleteSeparableRealReadbackFrontier [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead densityRead windowRead dyadicRead sealRead
      frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont M K completionRead →
        Cont M D densityRead →
          Cont completionRead densityRead windowRead →
            Cont windowRead R dyadicRead →
              Cont dyadicRead W sealRead →
                Cont sealRead R frontierRead →
                  PkgSig bundle G pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                              hsame row W ∨ hsame row dyadicRead ∨ hsame row sealRead ∨
                                hsame row frontierRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont completionRead densityRead windowRead ∧
                              Cont windowRead R dyadicRead ∧ Cont dyadicRead W sealRead ∧
                                Cont sealRead R frontierRead ∧ PkgSig bundle G pkg ∧
                                  PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier completionRoute densityRoute windowRoute dyadicRoute sealRoute frontierRoute
    provenancePkg localNamePkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed MUnary DUnary densityRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed completionUnary densityUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary RUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary WUnary sealRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed sealUnary RUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
              hsame row W ∨ hsame row dyadicRead ∨ hsame row sealRead ∨
                hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completionRead densityRead windowRead ∧
              Cont windowRead R dyadicRead ∧ Cont dyadicRead W sealRead ∧
                Cont sealRead R frontierRead ∧ PkgSig bundle G pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, dyadicRoute, sealRoute, frontierRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, frontierUnary⟩

end BEDC.Derived.PolishSpaceUp

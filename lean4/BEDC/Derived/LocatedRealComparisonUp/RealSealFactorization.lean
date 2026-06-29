import BEDC.Derived.LocatedRealComparisonUp.NameCertObligations

namespace BEDC.Derived.LocatedRealComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedRealComparisonCarrier_real_seal_factorization [AskSetup] [PackageSetup]
    {L0 L1 W R0 R1 D0 D1 B A H C P N endpointPair sharedWindow leftRead rightRead
      leftDyadic rightDyadic comparisonRead handoffRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealComparisonCarrier L0 L1 W R0 R1 D0 D1 B A H C P N bundle pkg ->
      Cont L0 L1 endpointPair ->
        Cont endpointPair W sharedWindow ->
          Cont sharedWindow R0 leftRead ->
            Cont sharedWindow R1 rightRead ->
              Cont leftRead D0 leftDyadic ->
                Cont rightRead D1 rightDyadic ->
                  Cont leftDyadic B comparisonRead ->
                    Cont comparisonRead A handoffRead ->
                      Cont handoffRead C publicRead ->
                        PkgSig bundle publicRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row L0 ∨ hsame row L1 ∨ hsame row W ∨
                                  hsame row R0 ∨ hsame row R1 ∨ hsame row D0 ∨
                                    hsame row D1 ∨ hsame row B ∨ hsame row A ∨
                                      hsame row C ∨ hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle publicRead pkg)
                              hsame ∧
                            UnaryHistory endpointPair ∧ UnaryHistory sharedWindow ∧
                              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                                UnaryHistory leftDyadic ∧ UnaryHistory rightDyadic ∧
                                  UnaryHistory comparisonRead ∧ UnaryHistory handoffRead ∧
                                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoute sharedRoute leftRoute rightRoute leftDyadicRoute
    rightDyadicRoute comparisonRoute handoffRoute publicRoute publicPkg
  obtain ⟨l0Unary, l1Unary, wUnary, r0Unary, r1Unary, d0Unary, d1Unary, bUnary, aUnary,
    _hUnary, cUnary, _pUnary, _nUnary, pPkg⟩ := carrier
  have endpointPairUnary : UnaryHistory endpointPair :=
    unary_cont_closed l0Unary l1Unary endpointRoute
  have sharedWindowUnary : UnaryHistory sharedWindow :=
    unary_cont_closed endpointPairUnary wUnary sharedRoute
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed sharedWindowUnary r0Unary leftRoute
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed sharedWindowUnary r1Unary rightRoute
  have leftDyadicUnary : UnaryHistory leftDyadic :=
    unary_cont_closed leftReadUnary d0Unary leftDyadicRoute
  have rightDyadicUnary : UnaryHistory rightDyadic :=
    unary_cont_closed rightReadUnary d1Unary rightDyadicRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed leftDyadicUnary bUnary comparisonRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed comparisonReadUnary aUnary handoffRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed handoffReadUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row L1 ∨ hsame row W ∨ hsame row R0 ∨ hsame row R1 ∨
              hsame row D0 ∨ hsame row D1 ∨ hsame row B ∨ hsame row A ∨ hsame row C ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨publicRead, hsame_refl publicRead, publicReadUnary⟩
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
                    (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg, publicPkg⟩
  }
  exact
    ⟨cert, endpointPairUnary, sharedWindowUnary, leftReadUnary, rightReadUnary,
      leftDyadicUnary, rightDyadicUnary, comparisonReadUnary, handoffReadUnary,
      publicReadUnary⟩

end BEDC.Derived.LocatedRealComparisonUp

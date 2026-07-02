import BEDC.Derived.CauchyCompletionOperatorUp.LedgerNonescape
import BEDC.Derived.RegularLimitUniquenessUp

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.Derived.RegularLimitUniquenessUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionOperatorCompleteMetricLimitUniquenessOutboundRef [AskSetup]
    [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead sealRead exportRead
      uniquenessRead : BHist}
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg ->
      RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
          readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
          bundle pkg ->
        Cont M U boundaryRead ->
          Cont B S finiteWindow ->
            Cont D Q separatedRead ->
              Cont separatedRead E sealRead ->
                Cont sealRead N exportRead ->
                  Cont exportRead endpoint uniquenessRead ->
                    PkgSig bundle uniquenessRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row uniquenessRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row B ∨ hsame row S ∨ hsame row D ∨
                              hsame row Q ∨ hsame row E ∨ hsame row N ∨ hsame row endpoint ∨
                                hsame row uniquenessRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M U boundaryRead ∧
                              Cont B S finiteWindow ∧ Cont D Q separatedRead ∧
                                Cont separatedRead E sealRead ∧ Cont sealRead N exportRead ∧
                                  Cont exportRead endpoint uniquenessRead ∧
                                    PkgSig bundle uniquenessRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet uniquenessCarrier boundaryRoute finiteRoute separatedRoute sealRoute exportRoute
    uniquenessRoute uniquenessPkg
  obtain ⟨mUnary, bUnary, uUnary, sUnary, _rUnary, dUnary, qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, nUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  obtain ⟨familyUnary, _diagonalLeftUnary, _diagonalRightUnary, thresholdUnary,
    readbackLeftUnary, readbackRightUnary, transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    _diagonalLeftThresholdReadback, _diagonalRightThresholdReadback, readbackLeftThresholdSeal,
    readbackRightThresholdSeal, sealComparison, separatedTransportEndpoint,
    _routeProvenanceEndpoint, _endpointPkg⟩ := uniquenessCarrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed mUnary uUnary boundaryRoute
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed bUnary sUnary finiteRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed dUnary qUnary separatedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedReadUnary eUnary sealRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed sealReadUnary nUnary exportRoute
  have sealLeftUnary : UnaryHistory sealLeft :=
    unary_cont_closed readbackLeftUnary thresholdUnary readbackLeftThresholdSeal
  have sealRightUnary : UnaryHistory sealRight :=
    unary_cont_closed readbackRightUnary thresholdUnary readbackRightThresholdSeal
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed sealLeftUnary sealRightUnary sealComparison
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separatedUnary transportUnary separatedTransportEndpoint
  have uniquenessUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed exportReadUnary endpointUnary uniquenessRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro uniquenessRead ⟨hsame_refl uniquenessRead, uniquenessUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, finiteRoute, separatedRoute, sealRoute, exportRoute,
          uniquenessRoute, uniquenessPkg⟩
  }

end BEDC.Derived.CauchyCompletionOperatorUp

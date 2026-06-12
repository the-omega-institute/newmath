import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowObserverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteWindowObserverCarrier [AskSetup] [PackageSetup]
    (O F I K D H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory O ∧ UnaryHistory F ∧ UnaryHistory I ∧ UnaryHistory K ∧
    UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont O F I ∧ Cont H C P ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem FiniteWindowObserverNameCertObligations [AskSetup] [PackageSetup]
    {O F I K D H C P N checkerRead acceptedRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowObserverCarrier O F I K D H C P N bundle pkg →
      Cont I K checkerRead →
        Cont checkerRead D acceptedRead →
          Cont acceptedRead N consumerRead →
            PkgSig bundle consumerRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row O ∨ hsame row F ∨ hsame row I ∨ hsame row K ∨
                      hsame row D ∨ hsame row checkerRead ∨ hsame row acceptedRead ∨
                        hsame row consumerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont I K checkerRead ∧
                      Cont checkerRead D acceptedRead ∧
                        Cont acceptedRead N consumerRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle consumerRead pkg)
                  hsame ∧
                UnaryHistory checkerRead ∧ UnaryHistory acceptedRead ∧
                  UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: FiniteWindowObserverCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier checkerRoute acceptedRoute consumerRoute consumerPkg
  obtain ⟨_observerUnary, _windowUnary, inscriptionUnary, checkerUnary, downstreamUnary,
    _transportUnary, _routeUnary, _provenanceUnary, localNameUnary, _windowRoute,
    _provenanceRoute, provenancePkg, _localNamePkg⟩ := carrier
  have checkerReadUnary : UnaryHistory checkerRead :=
    unary_cont_closed inscriptionUnary checkerUnary checkerRoute
  have acceptedReadUnary : UnaryHistory acceptedRead :=
    unary_cont_closed checkerReadUnary downstreamUnary acceptedRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed acceptedReadUnary localNameUnary consumerRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
          ⟨source.right, checkerRoute, acceptedRoute, consumerRoute, provenancePkg,
            consumerPkg⟩
    }
  · exact ⟨checkerReadUnary, acceptedReadUnary, consumerReadUnary⟩

theorem FiniteWindowObserverCarrierTransport [AskSetup] [PackageSetup]
    {O F I K D H C P N O' F' I' K' D' H' C' P' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowObserverCarrier O F I K D H C P N bundle pkg ->
      FiniteWindowObserverCarrier O' F' I' K' D' H' C' P' N' bundle pkg ->
        hsame O O' -> hsame F F' -> hsame I I' -> hsame K K' ->
          hsame D D' -> hsame P P' -> hsame N N' ->
            UnaryHistory O' ∧ UnaryHistory F' ∧ UnaryHistory I' ∧ UnaryHistory K' ∧
              UnaryHistory D' ∧ PkgSig bundle P' pkg ∧ PkgSig bundle N' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier _carrierTarget sameO sameF sameI sameK sameD _sameP _sameN
  obtain ⟨observerUnary, windowUnary, inscriptionUnary, checkerUnary, downstreamUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary, _windowRoute,
    _provenanceRoute, _provenancePkg, _localNamePkg⟩ := carrier
  obtain ⟨_observerTargetUnary, _windowTargetUnary, _inscriptionTargetUnary,
    _checkerTargetUnary, _downstreamTargetUnary, _transportTargetUnary, _routeTargetUnary,
    _provenanceTargetUnary, _localNameTargetUnary, _windowTargetRoute,
    _provenanceTargetRoute, provenanceTargetPkg, localNameTargetPkg⟩ := _carrierTarget
  exact
    ⟨unary_transport observerUnary sameO, unary_transport windowUnary sameF,
      unary_transport inscriptionUnary sameI, unary_transport checkerUnary sameK,
      unary_transport downstreamUnary sameD, provenanceTargetPkg, localNameTargetPkg⟩

end BEDC.Derived.FiniteWindowObserverUp

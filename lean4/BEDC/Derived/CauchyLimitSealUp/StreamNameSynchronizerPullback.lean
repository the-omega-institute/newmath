import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_streamname_synchronizer_pullback [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      budgetRead completionRead synchronizerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg →
      Cont schedule source window →
        Cont window dyadic budgetRead →
          Cont budgetRead diagonal completionRead →
            Cont completionRead endpoint synchronizerRead →
              hsame dyadic budgetRead →
                UnaryHistory window ∧ UnaryHistory budgetRead ∧
                  UnaryHistory completionRead ∧ UnaryHistory synchronizerRead ∧
                    hsame sealRow completionRead ∧
                      hsame endpoint (append provenance localCert) ∧
                        PkgSig bundle endpoint pkg ∧
                          SemanticNameCert
                            (fun row : BHist =>
                              hsame row synchronizerRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row synchronizerRead ∧
                                Cont completionRead endpoint synchronizerRead)
                            (fun row : BHist =>
                              hsame row synchronizerRead ∧ PkgSig bundle endpoint pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier scheduleSourceWindow windowDyadicBudget budgetDiagonalCompletion
    completionEndpointSynchronizer sameDyadicBudget
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicBudget
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetUnary diagonalUnary budgetDiagonalCompletion
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed completionUnary endpointUnary completionEndpointSynchronizer
  have sealSameCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicBudget (hsame_refl diagonal) dyadicDiagonalSeal
      budgetDiagonalCompletion
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row synchronizerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row synchronizerRead ∧ Cont completionRead endpoint synchronizerRead)
        (fun row : BHist => hsame row synchronizerRead ∧ PkgSig bundle endpoint pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro synchronizerRead
            (And.intro (hsame_refl synchronizerRead) synchronizerUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact And.intro source.left completionEndpointSynchronizer
      ledger_sound := by
        intro _row source
        exact And.intro source.left endpointPkg
    }
  exact
    ⟨windowUnary, budgetUnary, completionUnary, synchronizerUnary, sealSameCompletion,
      sameEndpoint, endpointPkg, cert⟩

end BEDC.Derived.CauchyLimitSealUp

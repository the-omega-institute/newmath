import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_zeta_basic_source_lock [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      zetaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      hsame zetaRead eta →
        UnaryHistory zetaRead ∧ UnaryHistory eta ∧ UnaryHistory functional ∧
          UnaryHistory application ∧ Cont eta functional application ∧
            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameZetaEta
  obtain ⟨etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, _gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, etaFunctionalApplication, _gammaApplicationReplay,
    _provenancePkg, namePkg⟩ := carrier
  have zetaReadUnary : UnaryHistory zetaRead :=
    unary_transport etaUnary (hsame_symm sameZetaEta)
  exact
    ⟨zetaReadUnary, etaUnary, functionalUnary, applicationUnary, etaFunctionalApplication,
      namePkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp

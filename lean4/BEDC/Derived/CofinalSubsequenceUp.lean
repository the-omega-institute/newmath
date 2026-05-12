import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalSubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CofinalSubsequenceCarrier [AskSetup] [PackageSetup]
    (source selector window dyadic regseq realSeal transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory selector ∧ UnaryHistory window ∧
    UnaryHistory dyadic ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont source selector window ∧
          Cont window dyadic transport ∧ Cont regseq dyadic realSeal ∧
            Cont realSeal provenance nameCert ∧ hsame realSeal (append regseq dyadic) ∧
              PkgSig bundle provenance pkg

theorem CofinalSubsequenceCarrier_regseqrat_consumer_boundary [AskSetup] [PackageSetup]
    {source selector window dyadic regseq realSeal transport route provenance nameCert
      consumerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
        provenance nameCert bundle pkg ->
      Cont regseq realSeal sealRead ->
        Cont sealRead consumerRead route ->
          UnaryHistory sealRead ∧ UnaryHistory route ∧ hsame realSeal (append regseq dyadic) ∧
            PkgSig bundle provenance pkg := by
  intro carrier sealReadRow _consumerRoute
  obtain ⟨_sourceUnary, _selectorUnary, _windowUnary, _dyadicUnary, regseqUnary,
    realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _nameCertUnary,
    _sourceSelectorWindow, _windowDyadicTransport, _regseqDyadicSeal,
    _sealProvenanceNameCert, sealSame, pkgSig⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary realSealUnary sealReadRow
  exact ⟨sealReadUnary, routeUnary, sealSame, pkgSig⟩

end BEDC.Derived.CofinalSubsequenceUp

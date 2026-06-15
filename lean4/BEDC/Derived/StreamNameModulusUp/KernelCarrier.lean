import BEDC.Derived.StreamNameModulusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StreamNameModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StreamNameModulusCarrier [AskSetup] [PackageSetup]
    (stream dyadic regseq realSeal modulus transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
    UnaryHistory realSeal ∧ UnaryHistory modulus ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        (∀ {precisionRead dyadicRead regseqRead : BHist},
          Cont precisionRead stream dyadicRead →
            Cont dyadicRead dyadic regseqRead →
              UnaryHistory dyadicRead ∧ UnaryHistory regseqRead) ∧
          PkgSig bundle provenance pkg

theorem StreamNameModulusCarrier_pointwise_stability [AskSetup] [PackageSetup]
    {stream dyadic regseq realSeal modulus transport replay provenance localName precisionRead
      dyadicRead regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StreamNameModulusCarrier stream dyadic regseq realSeal modulus transport replay provenance
        localName bundle pkg →
      Cont precisionRead stream dyadicRead →
        Cont dyadicRead dyadic regseqRead →
          PkgSig bundle provenance pkg →
            UnaryHistory stream ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
              UnaryHistory dyadicRead ∧ UnaryHistory regseqRead ∧
                Cont precisionRead stream dyadicRead ∧ Cont dyadicRead dyadic regseqRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier precisionStreamRoute dyadicRegseqRoute provenancePkg
  obtain ⟨streamUnary, dyadicUnary, regseqUnary, _realSealUnary, _modulusUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, routeClosed,
    _carrierPkg⟩ := carrier
  have readClosure : UnaryHistory dyadicRead ∧ UnaryHistory regseqRead :=
    routeClosed precisionStreamRoute dyadicRegseqRoute
  exact
    ⟨streamUnary, dyadicUnary, regseqUnary, readClosure.left, readClosure.right,
      precisionStreamRoute, dyadicRegseqRoute, provenancePkg⟩

end BEDC.Derived.StreamNameModulusUp

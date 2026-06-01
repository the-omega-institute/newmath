import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCauchyUniformCompleteHandoff [AskSetup] [PackageSetup]
    {source finiteLeft finiteRight hitLeft hitRight distLeft distRight realSeal transport replay
      provenance name completeRead cauchyRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier source finiteLeft finiteRight hitLeft hitRight distLeft distRight realSeal
        transport replay provenance name bundle pkg →
      Cont source finiteLeft completeRead →
        Cont completeRead replay cauchyRead →
          Cont cauchyRead provenance finalRead →
            PkgSig bundle finalRead pkg →
              UnaryHistory completeRead ∧ UnaryHistory cauchyRead ∧
                UnaryHistory finalRead ∧ Cont source finiteLeft completeRead ∧
                  Cont completeRead replay cauchyRead ∧
                    Cont cauchyRead provenance finalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sourceFiniteComplete completeReplayCauchy cauchyProvenanceFinal finalPkg
  obtain ⟨sourceUnary, finiteLeftUnary, _finiteRightUnary, _hitLeftUnary, _hitRightUnary,
    _distLeftUnary, _distRightUnary, _realSealUnary, _transportUnary, replayUnary,
    provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed sourceUnary finiteLeftUnary sourceFiniteComplete
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed completeUnary replayUnary completeReplayCauchy
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed cauchyUnary provenanceUnary cauchyProvenanceFinal
  exact
    ⟨completeUnary, cauchyUnary, finalUnary, sourceFiniteComplete, completeReplayCauchy,
      cauchyProvenanceFinal, provenancePkg, finalPkg⟩

end BEDC.Derived.HyperspaceUp

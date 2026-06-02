import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive ClosedBoundedIntervalSourceReadbackRoute
    (stream readback sealRow transport replay : BHist) : BHist → Prop where
  | streamRow :
      ClosedBoundedIntervalSourceReadbackRoute stream readback sealRow transport replay stream
  | readbackRow :
      ClosedBoundedIntervalSourceReadbackRoute stream readback sealRow transport replay readback
  | sealRowRoute :
      ClosedBoundedIntervalSourceReadbackRoute stream readback sealRow transport replay sealRow
  | replayed :
      Cont transport replay route →
        ClosedBoundedIntervalSourceReadbackRoute stream readback sealRow transport replay route

theorem ClosedBoundedIntervalPacket_source_readback_stability [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      ClosedBoundedIntervalSourceReadbackRoute stream readback sealRow transport replay route →
        UnaryHistory route ∧
          (hsame route stream ∨ hsame route readback ∨ hsame route sealRow ∨
            Cont transport replay route) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sourceRoute
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute,
    _containmentRoute, _sealRoute, _replayRoute, _nameRoute, _provenancePkg,
    _localNamePkg⟩ := packet
  cases sourceRoute with
  | streamRow =>
      exact ⟨streamUnary, Or.inl (hsame_refl stream)⟩
  | readbackRow =>
      exact ⟨readbackUnary, Or.inr (Or.inl (hsame_refl readback))⟩
  | sealRowRoute =>
      exact ⟨sealRowUnary, Or.inr (Or.inr (Or.inl (hsame_refl sealRow)))⟩
  | replayed replayRoute =>
      exact
        ⟨unary_cont_closed transportUnary replayUnary replayRoute,
          Or.inr (Or.inr (Or.inr replayRoute))⟩

end BEDC.Derived.ClosedboundedintervalUp

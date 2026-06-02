import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalRootSourceLedger [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame append Cont ProbeBundle Pkg PkgSig
  BEDC.Derived.ClosedboundedintervalUp.ClosedBoundedIntervalPacket lower upper order rational
      dyadic stream readback sealRow transport replay provenance localName exported bundle pkg ∧
    hsame ledger
      (append (append (append lower upper) order)
        (append (append rational dyadic) (append stream readback))) ∧
      Cont transport replay provenance ∧ PkgSig bundle localName pkg

theorem ClosedBoundedIntervalRootSourceLedger_exactness [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalRootSourceLedger lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported ledger bundle pkg →
      UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
        UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
          UnaryHistory readback ∧ UnaryHistory ledger ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist hsame append Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro ledgerWitness
  obtain ⟨packet, ledgerSame, replayRoute, localNamePkg⟩ := ledgerWitness
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _packetReplayRoute, _nameRoute, provenancePkg, _packetLocalNamePkg⟩ := packet
  have lowerUpperUnary : UnaryHistory (append lower upper) :=
    unary_append_closed lowerUnary upperUnary
  have lowerUpperOrderUnary : UnaryHistory (append (append lower upper) order) :=
    unary_append_closed lowerUpperUnary orderUnary
  have rationalDyadicUnary : UnaryHistory (append rational dyadic) :=
    unary_append_closed rationalUnary dyadicUnary
  have streamReadbackUnary : UnaryHistory (append stream readback) :=
    unary_append_closed streamUnary readbackUnary
  have rightLedgerUnary :
      UnaryHistory (append (append rational dyadic) (append stream readback)) :=
    unary_append_closed rationalDyadicUnary streamReadbackUnary
  have sourceLedgerUnary :
      UnaryHistory
        (append (append (append lower upper) order)
          (append (append rational dyadic) (append stream readback))) :=
    unary_append_closed lowerUpperOrderUnary rightLedgerUnary
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport sourceLedgerUnary (hsame_symm ledgerSame)
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, ledgerUnary, replayRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.ClosedBoundedIntervalUp

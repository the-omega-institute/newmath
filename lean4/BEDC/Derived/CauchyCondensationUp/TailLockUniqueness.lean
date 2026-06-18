import BEDC.Derived.CauchyCondensationUp.DyadicBlockHandoff

namespace BEDC.Derived.CauchyCondensationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCondensationCarrier_tail_lock_uniqueness [AskSetup] [PackageSetup]
    {source windows blocks sums tails readback sealRow transportRow replayRow provenance localName
      sealRead leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCondensationCarrier source windows blocks sums tails readback sealRow transportRow replayRow
        provenance localName bundle pkg →
      UnaryHistory readback →
        Cont readback sealRow leftRead →
          Cont readback sealRow rightRead →
            PkgSig bundle leftRead pkg →
              PkgSig bundle rightRead pkg →
                hsame leftRead rightRead ∧ UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier readbackUnary leftRoute rightRoute _leftPkg _rightPkg
  obtain ⟨_sourceUnary, _windowsUnary, _blocksUnary, _sumsUnary, _tailsUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    localNamePkg⟩ := carrier
  have sameReads : hsame leftRead rightRead :=
    cont_deterministic leftRoute rightRoute
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed readbackUnary sealUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed readbackUnary sealUnary rightRoute
  exact ⟨sameReads, leftUnary, rightUnary, provenancePkg, localNamePkg⟩

end BEDC.Derived.CauchyCondensationUp

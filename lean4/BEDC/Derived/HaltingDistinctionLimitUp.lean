import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HaltingDistinctionLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HaltingDistinctionLimitCarrier [AskSetup] [PackageSetup]
    (program input trace diagonal transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory program ∧ UnaryHistory input ∧ UnaryHistory trace ∧
    UnaryHistory diagonal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont input trace diagonal ∧
        Cont diagonal transport route ∧ Cont route provenance nameRow ∧
          hsame diagonal (append input trace) ∧ PkgSig bundle nameRow pkg

theorem HaltingDistinctionLimitCarrier_route_surface [AskSetup] [PackageSetup]
    {program input trace diagonal transport route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionLimitCarrier program input trace diagonal transport route provenance
        nameRow bundle pkg ->
      UnaryHistory diagonal ∧ UnaryHistory route ∧ UnaryHistory nameRow ∧
        Cont input trace diagonal ∧ Cont diagonal transport route ∧
          Cont route provenance nameRow ∧ hsame diagonal (append input trace) ∧
            PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier
  obtain ⟨_programUnary, _inputUnary, _traceUnary, diagonalUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, inputTraceDiagonal,
    diagonalTransportRoute, routeProvenanceNameRow, sameDiagonal, namePkg⟩ := carrier
  exact
    ⟨diagonalUnary, routeUnary, nameRowUnary, inputTraceDiagonal,
      diagonalTransportRoute, routeProvenanceNameRow, sameDiagonal, namePkg⟩

end BEDC.Derived.HaltingDistinctionLimitUp

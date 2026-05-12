import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformSpacePacket [AskSetup] [PackageSetup]
    (point entourage diagonal refinement symmetry composition transport provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory point ∧ UnaryHistory entourage ∧ UnaryHistory diagonal ∧
    UnaryHistory refinement ∧ UnaryHistory symmetry ∧ UnaryHistory composition ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont point entourage diagonal ∧ Cont diagonal refinement symmetry ∧
          Cont symmetry composition transport ∧ Cont transport provenance name ∧
            PkgSig bundle name pkg

theorem UniformSpacePacket_filterbase_diagonal_obligation [AskSetup] [PackageSetup]
    {point entourage diagonal refinement symmetry composition transport provenance name
      filterbase : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformSpacePacket point entourage diagonal refinement symmetry composition transport provenance
        name bundle pkg ->
      Cont diagonal refinement filterbase ->
        PkgSig bundle filterbase pkg ->
          UnaryHistory point ∧ UnaryHistory entourage ∧ UnaryHistory diagonal ∧
            UnaryHistory refinement ∧ UnaryHistory filterbase ∧
              Cont point entourage diagonal ∧ Cont diagonal refinement filterbase ∧
                PkgSig bundle filterbase pkg := by
  intro packet diagonalRefinementFilterbase filterbasePkg
  obtain ⟨pointUnary, entourageUnary, diagonalUnary, refinementUnary, _symmetryUnary,
    _compositionUnary, _transportUnary, _provenanceUnary, _nameUnary, pointEntourageDiagonal,
    _diagonalRefinementSymmetry, _symmetryCompositionTransport, _transportProvenanceName,
    _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbase :=
    unary_cont_closed diagonalUnary refinementUnary diagonalRefinementFilterbase
  exact
    ⟨pointUnary, entourageUnary, diagonalUnary, refinementUnary, filterbaseUnary,
      pointEntourageDiagonal, diagonalRefinementFilterbase, filterbasePkg⟩

end BEDC.Derived.UniformSpaceUp

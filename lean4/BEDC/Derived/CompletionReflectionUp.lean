import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionReflectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionReflectionPacket [AskSetup] [PackageSetup]
    (completion universal separated diagonal regular sealRow transport route package provenance
      cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory completion ∧ UnaryHistory universal ∧ UnaryHistory separated ∧
    UnaryHistory diagonal ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory package ∧
        UnaryHistory provenance ∧ UnaryHistory cert ∧ Cont completion universal package ∧
          Cont transport route provenance ∧ PkgSig bundle cert pkg

theorem CompletionReflectionPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          UnaryHistory reflected ∧ UnaryHistory sealRow ∧ UnaryHistory completion ∧
            UnaryHistory separated ∧ hsame reflected sealRow ∧ Cont diagonal regular reflected ∧
              Cont completion universal package ∧ PkgSig bundle cert pkg := by
  intro packet reflectedRow reflectedSame
  obtain ⟨completionUnary, _universalUnary, separatedUnary, diagonalUnary, regularUnary,
    sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    packageRow, _provenanceRow, certSig⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have sealUnary' : UnaryHistory sealRow :=
    unary_transport reflectedUnary reflectedSame
  exact
    ⟨reflectedUnary, sealUnary', completionUnary, separatedUnary, reflectedSame,
      reflectedRow, packageRow, certSig⟩

end BEDC.Derived.CompletionReflectionUp

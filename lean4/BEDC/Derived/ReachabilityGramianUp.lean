import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# ReachabilityGramianUp finite carrier.
-/

namespace BEDC.Derived.ReachabilityGramianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ReachabilityGramianBHistCarrier [AskSetup] [PackageSetup]
    (transition control horizon gramian transport route provenance cert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory transition ∧ UnaryHistory control ∧ UnaryHistory horizon ∧
    UnaryHistory gramian ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
        Cont transport route endpoint ∧ PkgSig bundle endpoint pkg

theorem ReachabilityGramianBHistCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {transition control horizon gramian transport route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReachabilityGramianBHistCarrier transition control horizon gramian transport route provenance
        cert endpoint bundle pkg ->
      UnaryHistory transition /\ UnaryHistory control /\ UnaryHistory horizon /\
        UnaryHistory gramian /\ UnaryHistory transport /\ UnaryHistory route /\
          UnaryHistory provenance /\ UnaryHistory cert /\ UnaryHistory endpoint /\
            Cont transport route endpoint /\ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    provenanceUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩ := carrier
  exact ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    provenanceUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩

theorem ReachabilityGramianBHistCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {transition control horizon gramian transport route provenance cert endpoint exportedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReachabilityGramianBHistCarrier transition control horizon gramian transport route provenance
        cert endpoint bundle pkg ->
      Cont endpoint route exportedRead ->
        PkgSig bundle exportedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row transition ∨ hsame row control ∨ hsame row horizon ∨
                  hsame row gramian ∨ hsame row endpoint ∨ hsame row exportedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont transport route endpoint ∧
                  Cont endpoint route exportedRead ∧ PkgSig bundle exportedRead pkg)
              hsame ∧
            UnaryHistory exportedRead ∧ Cont transport route endpoint ∧
              Cont endpoint route exportedRead ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle exportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier endpointExport exportedPackage
  obtain ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    _provenanceUnary, _certUnary, endpointUnary, endpointRoute, endpointPackage⟩ := carrier
  have exportedUnary : UnaryHistory exportedRead :=
    unary_cont_closed endpointUnary routeUnary endpointExport
  have exportedSource :
      hsame exportedRead exportedRead ∧ UnaryHistory exportedRead :=
    ⟨hsame_refl exportedRead, exportedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row transition ∨ hsame row control ∨ hsame row horizon ∨
              hsame row gramian ∨ hsame row endpoint ∨ hsame row exportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont transport route endpoint ∧
              Cont endpoint route exportedRead ∧ PkgSig bundle exportedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportedRead exportedSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, endpointExport, exportedPackage⟩
  }
  exact
    ⟨cert, exportedUnary, endpointRoute, endpointExport, endpointPackage, exportedPackage⟩

end BEDC.Derived.ReachabilityGramianUp

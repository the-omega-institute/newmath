import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_candidate_mediated_closedness_ledger
    [AskSetup] [PackageSetup] {S U V B R G K H C P N substRead betaRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont S V substRead ->
        Cont B R betaRead ->
          Cont substRead betaRead ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory B ∧
                UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory substRead ∧
                  UnaryHistory betaRead ∧ UnaryHistory ledgerRead ∧ Cont S U V ∧
                    Cont V G K ∧ Cont B R betaRead ∧
                      Cont substRead betaRead ledgerRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier substReadRoute betaReadRoute ledgerReadRoute ledgerReadPkg
  obtain ⟨SUnary, UUnary, VUnary, BUnary, RUnary, GUnary, KUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, shiftSubstitution, generatorPackage, _betaRoute, pkgSig⟩ :=
      carrier
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed SUnary VUnary substReadRoute
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed BUnary RUnary betaReadRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed substReadUnary betaReadUnary ledgerReadRoute
  exact
    ⟨SUnary, UUnary, VUnary, BUnary, RUnary, GUnary, KUnary, substReadUnary,
      betaReadUnary, ledgerReadUnary, shiftSubstitution, generatorPackage, betaReadRoute,
      ledgerReadRoute, pkgSig, ledgerReadPkg⟩

end BEDC.Derived.MetaCICClosureTraceUp

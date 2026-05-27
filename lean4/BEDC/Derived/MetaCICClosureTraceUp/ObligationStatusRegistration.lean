import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_obligation_status_registration
    [AskSetup] [PackageSetup] {S U V B R G K H C P N substRead betaRead ledgerRead
      statusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg →
      Cont S V substRead →
        Cont B R betaRead →
          Cont substRead betaRead ledgerRead →
            Cont ledgerRead N statusRead →
              PkgSig bundle ledgerRead pkg →
                PkgSig bundle statusRead pkg →
                  UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory B ∧
                    UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory K ∧
                      UnaryHistory substRead ∧ UnaryHistory betaRead ∧
                        UnaryHistory ledgerRead ∧ UnaryHistory statusRead ∧ Cont S U V ∧
                          Cont V G K ∧ Cont B R betaRead ∧
                            Cont substRead betaRead ledgerRead ∧
                              Cont ledgerRead N statusRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle ledgerRead pkg ∧ PkgSig bundle statusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier substRoute betaRoute ledgerRoute statusRoute ledgerPkg statusPkg
  obtain ⟨SUnary, UUnary, VUnary, BUnary, RUnary, GUnary, KUnary, _HUnary, _CUnary,
    _PUnary, NUnary, shiftSubstitution, generatorPackage, _betaCarrierRoute, pkgSig⟩ :=
      carrier
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed SUnary VUnary substRoute
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed BUnary RUnary betaRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed substReadUnary betaReadUnary ledgerRoute
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed ledgerReadUnary NUnary statusRoute
  exact
    ⟨SUnary, UUnary, VUnary, BUnary, RUnary, GUnary, KUnary, substReadUnary,
      betaReadUnary, ledgerReadUnary, statusReadUnary, shiftSubstitution, generatorPackage,
      betaRoute, ledgerRoute, statusRoute, pkgSig, ledgerPkg, statusPkg⟩

end BEDC.Derived.MetaCICClosureTraceUp

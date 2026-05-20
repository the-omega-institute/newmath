import BEDC.Derived.RealUp.NameSealSourceFactorization

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealRegseqratFiniteRequestFusion [AskSetup] [PackageSetup]
    {dyadic stream regular ledger sealRow transport route provenance nameRow sourceRead
      requestRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameSealCarrier dyadic stream regular ledger sealRow transport route provenance nameRow
        bundle pkg ->
      Cont stream dyadic sourceRead ->
        Cont sourceRead sealRow requestRead ->
          PkgSig bundle sourceRead pkg ->
            PkgSig bundle requestRead pkg ->
              UnaryHistory stream ∧ UnaryHistory dyadic ∧ UnaryHistory regular ∧
                UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory sourceRead ∧
                  UnaryHistory requestRead ∧ Cont stream dyadic sourceRead ∧
                    Cont sourceRead sealRow requestRead ∧ PkgSig bundle sealRow pkg ∧
                      PkgSig bundle sourceRead pkg ∧ PkgSig bundle requestRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceRoute requestRoute sourcePkg requestPkg
  obtain ⟨dyadicUnary, streamUnary, regularUnary, ledgerUnary, _nameRowUnary,
    _regularRoute, sealRoute, _transportRoute, _provenanceRoute, sealPkg⟩ := carrier
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed regularUnary ledgerUnary sealRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed streamUnary dyadicUnary sourceRoute
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed sourceUnary sealUnary requestRoute
  exact
    ⟨streamUnary, dyadicUnary, regularUnary, ledgerUnary, sealUnary, sourceUnary,
      requestUnary, sourceRoute, requestRoute, sealPkg, sourcePkg, requestPkg⟩

end BEDC.Derived.RealUp

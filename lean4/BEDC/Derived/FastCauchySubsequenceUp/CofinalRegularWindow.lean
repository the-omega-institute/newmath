import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalRegularWindow [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead tailRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W tailRead ->
                Cont tailRead E sealRead ->
                  PkgSig bundle sealRead pkg ->
                    UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                      UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                        UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                          Cont fastRead R regularRead ∧ Cont regularRead W tailRead ∧
                            Cont tailRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceModulus modulusSelector selectorFast fastRegular regularTail tailSeal
    sealPkg
  obtain ⟨sourceUnary, modulusUnary, selectorUnary, fastUnary, regularUnary, tailUnary,
    sealUnary, _histUnary, _certUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    localNamePkg⟩ := carrier
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary modulusUnary sourceModulus
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusReadUnary selectorUnary modulusSelector
  have fastReadUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorReadUnary fastUnary selectorFast
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed fastReadUnary regularUnary fastRegular
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed regularReadUnary tailUnary regularTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary sealUnary tailSeal
  exact
    ⟨modulusReadUnary, selectorReadUnary, fastReadUnary, regularReadUnary, tailReadUnary,
      sealReadUnary, fastRegular, regularTail, tailSeal, provenancePkg, localNamePkg, sealPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.RegularCauchyLocatedOrderUp.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLocatedOrderCarrier [AskSetup] [PackageSetup]
    (left right window tolerance comparison sealRow transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory window ∧
    UnaryHistory tolerance ∧ UnaryHistory comparison ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont left window tolerance ∧ Cont tolerance comparison sealRow ∧
          PkgSig bundle provenance pkg

theorem RegularCauchyLocatedOrderCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {left right window tolerance comparison sealRow transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLocatedOrderCarrier left right window tolerance comparison sealRow transport
        replay provenance name bundle pkg ->
      UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory window ∧
        UnaryHistory tolerance ∧ UnaryHistory comparison ∧ UnaryHistory sealRow ∧
          Cont left window tolerance ∧ Cont tolerance comparison sealRow ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨leftUnary, rightUnary, windowUnary, toleranceUnary, comparisonUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, sourceRoute, sealRoute,
    provenancePkg⟩ := carrier
  exact
    ⟨leftUnary, rightUnary, windowUnary, toleranceUnary, comparisonUnary, sealUnary,
      sourceRoute, sealRoute, provenancePkg⟩

theorem RegularCauchyLocatedOrderCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {left right window tolerance comparison sealRow transport replay provenance name
      leftWindow comparisonRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLocatedOrderCarrier left right window tolerance comparison sealRow transport
        replay provenance name bundle pkg ->
      Cont left window leftWindow ->
        Cont leftWindow tolerance comparisonRead ->
          Cont comparisonRead sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory leftWindow ∧ UnaryHistory comparisonRead ∧
                UnaryHistory sealRead ∧ Cont left window leftWindow ∧
                  Cont leftWindow tolerance comparisonRead ∧
                    Cont comparisonRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier leftWindowRoute comparisonRoute sealReadRoute sealReadPkg
  obtain
    ⟨leftUnary, _rightUnary, windowUnary, toleranceUnary, _comparisonUnary, sealUnary,
      _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _sourceRoute,
        _sealRoute, provenancePkg⟩ := carrier
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed leftUnary windowUnary leftWindowRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed leftWindowUnary toleranceUnary comparisonRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed comparisonReadUnary sealUnary sealReadRoute
  exact
    ⟨leftWindowUnary, comparisonReadUnary, sealReadUnary, leftWindowRoute, comparisonRoute,
      sealReadRoute, provenancePkg, sealReadPkg⟩

end BEDC.Derived.RegularCauchyLocatedOrderUp

import BEDC.Derived.CanonicalTailChoiceUp.Nonescape
import BEDC.FKernel.Cont

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_scoped_source_discipline [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N tailRead sealRead boundaryRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont I T tailRead →
        Cont tailRead S sealRead →
          Cont sealRead R boundaryRead →
            Cont boundaryRead C0 sourceRead →
              PkgSig bundle sourceRead pkg →
                UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory sourceRead ∧
                    Cont I T tailRead ∧ Cont tailRead S sealRead ∧
                      Cont sealRead R boundaryRead ∧ Cont boundaryRead C0 sourceRead ∧
                        PkgSig bundle N pkg ∧ PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier tailRoute sealRoute boundaryRoute sourceRoute sourcePkg
  obtain ⟨_mUnary, _eUnary, iUnary, tUnary, sUnary, rUnary, _hUnary, c0Unary,
    _pUnary, _nUnary, _pPkg, namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed iUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnary rUnary boundaryRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed boundaryUnary c0Unary sourceRoute
  exact
    ⟨tailUnary, sealUnary, boundaryUnary, sourceUnary, tailRoute, sealRoute,
      boundaryRoute, sourceRoute, namePkg, sourcePkg⟩

end BEDC.Derived.CanonicalTailChoiceUp

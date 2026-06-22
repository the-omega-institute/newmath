import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureCarrier_located_cauchy_filter_handoff [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N endpointRead radiusRead filterRead windowRead readbackRead
      locatedTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont R M endpointRead →
        Cont endpointRead D radiusRead →
          Cont radiusRead U filterRead →
            Cont filterRead S windowRead →
              Cont windowRead Q readbackRead →
                Cont readbackRead F locatedTail →
                  PkgSig bundle locatedTail pkg →
                    UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory U ∧
                      UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                        UnaryHistory endpointRead ∧ UnaryHistory radiusRead ∧
                          UnaryHistory filterRead ∧ UnaryHistory windowRead ∧
                            UnaryHistory readbackRead ∧ UnaryHistory locatedTail ∧
                              Cont R M endpointRead ∧ Cont endpointRead D radiusRead ∧
                                Cont radiusRead U filterRead ∧ Cont filterRead S windowRead ∧
                                  Cont windowRead Q readbackRead ∧
                                    Cont readbackRead F locatedTail ∧
                                      PkgSig bundle P pkg ∧
                                        PkgSig bundle locatedTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointCont radiusCont filterCont windowCont readbackCont locatedCont
    locatedPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed rUnary mUnary endpointCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed endpointUnary dUnary radiusCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed radiusUnary uUnary filterCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterUnary sUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have locatedUnary : UnaryHistory locatedTail :=
    unary_cont_closed readbackUnary fUnary locatedCont
  exact
    ⟨rUnary, mUnary, dUnary, uUnary, fUnary, sUnary, qUnary, endpointUnary, radiusUnary,
      filterUnary, windowUnary, readbackUnary, locatedUnary, endpointCont, radiusCont,
      filterCont, windowCont, readbackCont, locatedCont, pPkg, locatedPkg⟩

end BEDC.Derived.RealUniformStructureUp

import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRegularCauchySequenceHandoff
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      regularFamily regularModulus regularWindow regularDyadic regularReadback regularGap
      regularSeal handoff selectorConsumer completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory regularFamily ->
        UnaryHistory regularModulus ->
          hsame regularWindow windows ->
            hsame regularDyadic dyadic ->
              hsame regularReadback readback ->
                hsame regularSeal realSeal ->
                  Cont regularFamily regularModulus regularWindow ->
                    Cont regularWindow regularDyadic handoff ->
                      Cont handoff readback selectorConsumer ->
                        Cont selectorConsumer realSeal completionRead ->
                          PkgSig bundle completionRead pkg ->
                            UnaryHistory handoff ∧ UnaryHistory selectorConsumer ∧
                              UnaryHistory completionRead ∧ hsame regularWindow windows ∧
                                hsame regularDyadic dyadic ∧ hsame regularReadback readback ∧
                                  hsame regularSeal realSeal ∧
                                    Cont regularWindow regularDyadic handoff ∧
                                      Cont handoff readback selectorConsumer ∧
                                        Cont selectorConsumer realSeal completionRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle hsame UnaryHistory
  intro carrier _regularFamilyUnary _regularModulusUnary sameWindow sameDyadic
    sameReadback sameSeal _familyModulusWindow windowDyadicHandoff handoffReadbackSelector
    selectorSealCompletion completionPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have _regularGapReflexive : hsame regularGap regularGap := hsame_refl regularGap
  have regularWindowUnary : UnaryHistory regularWindow :=
    unary_transport_symm windowsUnary sameWindow
  have regularDyadicUnary : UnaryHistory regularDyadic :=
    unary_transport_symm dyadicUnary sameDyadic
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed regularWindowUnary regularDyadicUnary windowDyadicHandoff
  have selectorUnary : UnaryHistory selectorConsumer :=
    unary_cont_closed handoffUnary readbackUnary handoffReadbackSelector
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed selectorUnary realSealUnary selectorSealCompletion
  exact
    ⟨handoffUnary, selectorUnary, completionUnary, sameWindow, sameDyadic, sameReadback,
      sameSeal, windowDyadicHandoff, handoffReadbackSelector, selectorSealCompletion,
      provenancePkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp

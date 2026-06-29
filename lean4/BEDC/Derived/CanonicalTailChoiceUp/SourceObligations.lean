import BEDC.Derived.CanonicalTailChoiceUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_source_obligations [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N indexRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory E →
        UnaryHistory T →
          UnaryHistory S →
            UnaryHistory N →
              PkgSig bundle N pkg →
                Cont M E indexRead →
                  Cont indexRead T tailRead →
                    Cont tailRead S sealRead →
                      PkgSig bundle sealRead pkg →
                        UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory T ∧
                          UnaryHistory S ∧ UnaryHistory indexRead ∧
                            UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                              Cont M E indexRead ∧ Cont indexRead T tailRead ∧
                                Cont tailRead S sealRead ∧ PkgSig bundle N pkg ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro mUnary eUnary tUnary sUnary _nUnary nPkg indexRoute tailRoute sealRoute sealPkg
  have _indexRow : hsame I I := hsame_refl I
  have _refusalRow : hsame R R := hsame_refl R
  have _transportRow : hsame H H := hsame_refl H
  have _replayRow : hsame C0 C0 := hsame_refl C0
  have _provenanceRow : hsame P P := hsame_refl P
  have indexUnary : UnaryHistory indexRead :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  exact
    ⟨mUnary, eUnary, tUnary, sUnary, indexUnary, tailUnary, sealUnary, indexRoute,
      tailRoute, sealRoute, nPkg, sealPkg⟩

end BEDC.Derived.CanonicalTailChoiceUp

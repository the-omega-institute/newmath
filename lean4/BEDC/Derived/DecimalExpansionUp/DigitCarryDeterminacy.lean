import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionDigitCarryDeterminacy [AskSetup] [PackageSetup]
    {D W V Q R E H C P N D' W' V' Q' R' E' H' C' P' N' window value handoff handoff'
      sealRead sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory D' ->
                UnaryHistory W' ->
                  UnaryHistory V' ->
                    UnaryHistory Q' ->
                      UnaryHistory R' ->
                        Cont D W window ->
                          Cont D' W' window ->
                            Cont window V value ->
                              Cont window V' value ->
                                Cont value Q handoff ->
                                  Cont value Q' handoff' ->
                                    Cont handoff R sealRead ->
                                      Cont handoff' R' sealRead' ->
                                        hsame Q Q' ->
                                          hsame R R' ->
                                            PkgSig bundle P pkg ->
                                              PkgSig bundle N pkg ->
                                                hsame handoff handoff' ∧
                                                  hsame sealRead sealRead' ∧
                                                    UnaryHistory handoff ∧
                                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary _dPrimeUnary _wPrimeUnary _vPrimeUnary
    _qPrimeUnary _rPrimeUnary digitWindow _digitWindowPrime windowValue _windowValuePrime
    valueHandoff valueHandoffPrime handoffSeal handoffSealPrime sameQ sameR _pkgP _pkgN
  cases sameQ
  cases sameR
  cases valueHandoff
  cases valueHandoffPrime
  cases handoffSeal
  cases handoffSealPrime
  have windowUnary : UnaryHistory window :=
    unary_cont_closed dUnary wUnary digitWindow
  have valueUnary : UnaryHistory value :=
    unary_cont_closed windowUnary vUnary windowValue
  have handoffUnary : UnaryHistory (append value Q) :=
    unary_cont_closed valueUnary qUnary rfl
  have sealUnary : UnaryHistory (append (append value Q) R) :=
    unary_cont_closed handoffUnary rUnary rfl
  exact ⟨hsame_refl (append value Q), hsame_refl (append (append value Q) R), handoffUnary,
    sealUnary⟩

end BEDC.Derived.DecimalExpansionUp

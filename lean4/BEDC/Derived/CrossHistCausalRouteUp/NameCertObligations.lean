import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CrossHistCausalRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CrossHistCausalRouteCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {observerA observerB causalRows maxRate symmetryGate nonEscapeGate trace _transport _access
      provenance localName routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory observerA ->
      UnaryHistory observerB ->
        UnaryHistory causalRows ->
          UnaryHistory maxRate ->
            UnaryHistory symmetryGate ->
              UnaryHistory nonEscapeGate ->
                UnaryHistory trace ->
                  UnaryHistory localName ->
                    Cont observerA observerB causalRows ->
                      Cont causalRows maxRate trace ->
                        Cont trace localName routeRead ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row observerA ∨ hsame row observerB ∨
                                      hsame row causalRows ∨ hsame row maxRate ∨
                                        hsame row symmetryGate ∨ hsame row nonEscapeGate ∨
                                          hsame row trace ∨ hsame row routeRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont observerA observerB causalRows ∧
                                      Cont causalRows maxRate trace ∧
                                        PkgSig bundle provenance pkg)
                                  hsame ∧
                                UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro observerAUnary observerBUnary _causalRowsUnary maxRateUnary _symmetryGateUnary
    _nonEscapeGateUnary _traceUnary localNameUnary observerRoute traceRoute routeRoute
    provenancePkg _localNamePkg
  have causalRowsUnary : UnaryHistory causalRows :=
    unary_cont_closed observerAUnary observerBUnary observerRoute
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed causalRowsUnary maxRateUnary traceRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed traceUnary localNameUnary routeRoute
  have routeSource :
      (fun row : BHist => hsame row routeRead ∧ UnaryHistory row) routeRead := by
    exact ⟨hsame_refl routeRead, routeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observerA ∨ hsame row observerB ∨ hsame row causalRows ∨
              hsame row maxRate ∨ hsame row symmetryGate ∨ hsame row nonEscapeGate ∨
                hsame row trace ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont observerA observerB causalRows ∧
              Cont causalRows maxRate trace ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro routeRead routeSource
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, observerRoute, traceRoute, provenancePkg⟩
    }
  exact ⟨cert, routeReadUnary⟩

end BEDC.Derived.CrossHistCausalRouteUp

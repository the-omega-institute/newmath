import BEDC.Derived.SubmartingaleUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SubmartingaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubmartingaleCarrier_stopping_window_handoff [AskSetup] [PackageSetup]
    {omega randomVar condExp filtration endpoint expectation comparison time transport replay
      provenance localName stopWindow stoppedRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubmartingaleCarrier omega randomVar condExp filtration endpoint expectation comparison time
        transport replay provenance localName bundle pkg →
      Cont endpoint comparison stopWindow →
        Cont stopWindow time stoppedRead →
          Cont stoppedRead replay handoffRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row omega ∨ hsame row randomVar ∨ hsame row condExp ∨
                        hsame row filtration ∨ hsame row endpoint ∨ hsame row comparison ∨
                          hsame row time ∨ hsame row stopWindow ∨
                            hsame row stoppedRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont endpoint comparison stopWindow ∧
                        Cont stopWindow time stoppedRead ∧
                          Cont stoppedRead replay handoffRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧ UnaryHistory stopWindow ∧ UnaryHistory stoppedRead ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: SubmartingaleCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier stopRoute stoppedRoute handoffRoute provenancePkg localNamePkg
  obtain ⟨_omegaUnary, _randomVarUnary, _condExpUnary, _filtrationUnary, endpointUnary,
    _expectationUnary, comparisonUnary, timeUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _localNameCarrierPkg⟩ := carrier
  have stopWindowUnary : UnaryHistory stopWindow :=
    unary_cont_closed endpointUnary comparisonUnary stopRoute
  have stoppedReadUnary : UnaryHistory stoppedRead :=
    unary_cont_closed stopWindowUnary timeUnary stoppedRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed stoppedReadUnary replayUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row omega ∨ hsame row randomVar ∨ hsame row condExp ∨
              hsame row filtration ∨ hsame row endpoint ∨ hsame row comparison ∨
                hsame row time ∨ hsame row stopWindow ∨
                  hsame row stoppedRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpoint comparison stopWindow ∧
              Cont stopWindow time stoppedRead ∧ Cont stoppedRead replay handoffRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffReadUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, stopRoute, stoppedRoute, handoffRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, stopWindowUnary, stoppedReadUnary, handoffReadUnary⟩

end BEDC.Derived.SubmartingaleUp

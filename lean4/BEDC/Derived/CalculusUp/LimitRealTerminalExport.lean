import BEDC.Derived.CalculusUp.ProductMetricForwardLink

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusLimitRealTerminalExport [AskSetup] [PackageSetup]
    {limit dyadic stream regSeq real derivative integral endpoint endpointRead limitRead
      dyadicRead scheduleRead regularRead terminalRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory limit →
      UnaryHistory dyadic →
        UnaryHistory stream →
          UnaryHistory regSeq →
            UnaryHistory real →
              UnaryHistory derivative →
                UnaryHistory integral →
                  UnaryHistory endpoint →
                    Cont derivative integral endpointRead →
                      Cont endpointRead limit limitRead →
                        Cont limitRead dyadic dyadicRead →
                          Cont dyadicRead stream scheduleRead →
                            Cont scheduleRead regSeq regularRead →
                              Cont regularRead real terminalRead →
                                PkgSig bundle provenance pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row terminalRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row limit ∨ hsame row dyadic ∨
                                          hsame row stream ∨ hsame row regSeq ∨
                                            hsame row real ∨ hsame row terminalRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont derivative integral endpointRead ∧
                                            Cont endpointRead limit limitRead ∧
                                              Cont limitRead dyadic dyadicRead ∧
                                                Cont dyadicRead stream scheduleRead ∧
                                                  Cont scheduleRead regSeq regularRead ∧
                                                    Cont regularRead real terminalRead ∧
                                                      PkgSig bundle provenance pkg)
                                      hsame ∧
                                    UnaryHistory endpointRead ∧ UnaryHistory limitRead ∧
                                      UnaryHistory dyadicRead ∧ UnaryHistory scheduleRead ∧
                                        UnaryHistory regularRead ∧
                                          UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro limitUnary dyadicUnary streamUnary regSeqUnary realUnary derivativeUnary integralUnary
    _endpointUnary endpointRoute limitRoute dyadicRoute scheduleRoute regularRoute terminalRoute
    provenancePkg
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed derivativeUnary integralUnary endpointRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed endpointReadUnary limitUnary limitRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed limitReadUnary dyadicUnary dyadicRoute
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed dyadicReadUnary streamUnary scheduleRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduleReadUnary regSeqUnary regularRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed regularReadUnary realUnary terminalRoute
  have sourceAtTerminal :
      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row) terminalRead := by
    exact ⟨hsame_refl terminalRead, terminalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row limit ∨ hsame row dyadic ∨ hsame row stream ∨ hsame row regSeq ∨
              hsame row real ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivative integral endpointRead ∧
              Cont endpointRead limit limitRead ∧ Cont limitRead dyadic dyadicRead ∧
                Cont dyadicRead stream scheduleRead ∧ Cont scheduleRead regSeq regularRead ∧
                  Cont regularRead real terminalRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceAtTerminal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, limitRoute, dyadicRoute, scheduleRoute, regularRoute,
          terminalRoute, provenancePkg⟩
  }
  exact
    ⟨cert, endpointReadUnary, limitReadUnary, dyadicReadUnary, scheduleReadUnary,
      regularReadUnary, terminalReadUnary⟩

end BEDC.Derived.CalculusUp

import BEDC.Derived.FableMachineClockUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

/-!
# FableMachineClockUp finite-row obligations.
-/

namespace BEDC.Derived.FableMachineClockUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def FableMachineClockCarrier
    (H I M S B T C P N selectedRead boundaryRead : BHist) : Prop :=
  UnaryHistory H ∧ UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory B ∧
    UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont I M selectedRead ∧ Cont selectedRead S boundaryRead ∧ Cont B T C ∧ Cont C P N

theorem FableMachineClockCarrier_step_ledger_exactness
    {H I M S B T C P N selectedRead boundaryRead : BHist} :
    FableMachineClockCarrier H I M S B T C P N selectedRead boundaryRead →
      UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory selectedRead ∧
        UnaryHistory boundaryRead ∧ Cont I M selectedRead ∧ Cont selectedRead S boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier
  cases carrier with
  | intro unaryH rest₁ =>
      cases rest₁ with
      | intro unaryI rest₂ =>
          cases rest₂ with
          | intro unaryM rest₃ =>
              cases rest₃ with
              | intro unaryS rest₄ =>
                  cases rest₄ with
                  | intro unaryB rest₅ =>
                      cases rest₅ with
                      | intro unaryT rest₆ =>
                          cases rest₆ with
                          | intro unaryC rest₇ =>
                              cases rest₇ with
                              | intro unaryP rest₈ =>
                                  cases rest₈ with
                                  | intro unaryN rest₉ =>
                                      cases rest₉ with
                                      | intro contIM rest₁₀ =>
                                          cases rest₁₀ with
                                          | intro contSelectedS contRest =>
                                              have unarySelected :
                                                  UnaryHistory selectedRead :=
                                                unary_cont_closed unaryI unaryM contIM
                                              have unaryBoundary :
                                                  UnaryHistory boundaryRead :=
                                                unary_cont_closed unarySelected unaryS
                                                  contSelectedS
                                              constructor
                                              · exact unaryI
                                              · constructor
                                                · exact unaryM
                                                · constructor
                                                  · exact unaryS
                                                  · constructor
                                                    · exact unarySelected
                                                    · constructor
                                                      · exact unaryBoundary
                                                      · constructor
                                                        · exact contIM
                                                        · exact contSelectedS

theorem FableMachineClockCarrier_no_global_clock_boundary
    {H I M S B T C P N selectedRead boundaryRead : BHist} :
    FableMachineClockCarrier H I M S B T C P N selectedRead boundaryRead →
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist => hsame row N ∧ Cont C P N)
          (fun row : BHist => hsame row N ∧ Cont B T C)
          hsame ∧
        UnaryHistory H ∧ UnaryHistory I ∧ UnaryHistory B ∧ UnaryHistory N ∧
          Cont B T C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory NameCert
  intro carrier
  cases carrier with
  | intro unaryH rest₁ =>
      cases rest₁ with
      | intro unaryI rest₂ =>
          cases rest₂ with
          | intro unaryM rest₃ =>
              cases rest₃ with
              | intro unaryS rest₄ =>
                  cases rest₄ with
                  | intro unaryB rest₅ =>
                      cases rest₅ with
                      | intro unaryT rest₆ =>
                          cases rest₆ with
                          | intro unaryC rest₇ =>
                              cases rest₇ with
                              | intro unaryP rest₈ =>
                                  cases rest₈ with
                                  | intro unaryN rest₉ =>
                                      cases rest₉ with
                                      | intro contIM rest₁₀ =>
                                          cases rest₁₀ with
                                          | intro contSelectedS rest₁₁ =>
                                              cases rest₁₁ with
                                              | intro contBTC contCPN =>
                                                  have cert :
                                                      SemanticNameCert
                                                        (fun row : BHist =>
                                                          hsame row N ∧ UnaryHistory row)
                                                        (fun row : BHist =>
                                                          hsame row N ∧ Cont C P N)
                                                        (fun row : BHist =>
                                                          hsame row N ∧ Cont B T C)
                                                        hsame := {
                                                    core := {
                                                      carrier_inhabited :=
                                                        Exists.intro N
                                                          (And.intro (hsame_refl N) unaryN)
                                                      equiv_refl := by
                                                        intro row source
                                                        exact hsame_refl row
                                                      equiv_symm := by
                                                        intro row other same
                                                        exact hsame_symm same
                                                      equiv_trans := by
                                                        intro row other third sameRO sameOT
                                                        exact hsame_trans sameRO sameOT
                                                      carrier_respects_equiv := by
                                                        intro row other same source
                                                        cases source with
                                                        | intro rowSameN rowUnary =>
                                                            constructor
                                                            · exact hsame_trans (hsame_symm same)
                                                                rowSameN
                                                            · exact unary_transport rowUnary same
                                                    }
                                                    pattern_sound := by
                                                      intro row source
                                                      exact And.intro source.left contCPN
                                                    ledger_sound := by
                                                      intro row source
                                                      exact And.intro source.left contBTC
                                                  }
                                                  constructor
                                                  · exact cert
                                                  · constructor
                                                    · exact unaryH
                                                    · constructor
                                                      · exact unaryI
                                                      · constructor
                                                        · exact unaryB
                                                        · constructor
                                                          · exact unaryN
                                                          · constructor
                                                            · exact contBTC
                                                            · exact contCPN

end BEDC.Derived.FableMachineClockUp

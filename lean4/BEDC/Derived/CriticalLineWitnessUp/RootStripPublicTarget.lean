import BEDC.Derived.CriticalLineWitnessUp.RootGammaRealDependency
import BEDC.Derived.CriticalLineWitnessUp.RootRefusalLedgerExactness
import BEDC.Derived.CriticalLineWitnessUp.RootStripSourceTotality

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_strip_public_target
    {Z S M R Q H C P N sourceRead realRead packageRead gammaRead refusalRead
      refusalGammaRead zetaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R realRead ->
          Cont sourceRead realRead packageRead ->
            Cont realRead Q gammaRead ->
              Cont N Q refusalRead ->
                Cont refusalRead C refusalGammaRead ->
                  Cont refusalRead H zetaRead ->
                    SemanticNameCert
                        (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                        (fun row : BHist => hsame row packageRead)
                        (fun row : BHist =>
                          hsame row packageRead ∧ Cont sourceRead realRead packageRead)
                        hsame ∧
                      SemanticNameCert
                          (fun row : BHist => hsame row gammaRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row R ∨ hsame row Q ∨
                              hsame row gammaRead)
                          (fun row : BHist =>
                            hsame row gammaRead ∧ Cont realRead Q gammaRead)
                          hsame ∧
                        SemanticNameCert
                            (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row refusalRead ∧ Cont N Q refusalRead)
                            (fun row : BHist =>
                              hsame row refusalRead ∧
                                Cont refusalRead C refusalGammaRead ∧
                                  Cont refusalRead H zetaRead)
                            hsame ∧
                          hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
                            Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert
  intro packet sourceRoute realRoute packageRoute gammaRoute refusalRoute refusalGammaRoute
    zetaRoute
  have sourceTarget :=
    CriticalLineWitnessCarrier_root_strip_source_totality packet sourceRoute realRoute
      packageRoute
  have gammaTarget :=
    CriticalLineWitnessCarrier_root_gamma_real_dependency packet realRoute gammaRoute
  have refusalTarget :=
    CriticalLineWitnessCarrier_root_refusal_ledger_exactness packet refusalRoute
      refusalGammaRoute zetaRoute
  obtain ⟨_unaryZ, _unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  exact ⟨sourceTarget.left, gammaTarget.left, refusalTarget.left, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp

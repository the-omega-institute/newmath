import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceConstructorLedgerExhaustion
    [AskSetup] [PackageSetup]
    {D S E P R H C Q N constructorRead eliminatorRead : BHist} :
    (packet : KernelInductiveAcceptanceUp) ->
      packet = KernelInductiveAcceptanceUp.mk D S E P R H C Q N ->
      UnaryHistory D ->
        UnaryHistory S ->
          UnaryHistory E ->
            Cont D S constructorRead ->
              Cont constructorRead E eliminatorRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row eliminatorRead ∧ UnaryHistory row)
                    (fun row : BHist => hsame row eliminatorRead ∧ Cont D S constructorRead)
                    (fun row : BHist =>
                      hsame row eliminatorRead ∧ Cont constructorRead E eliminatorRead)
                    hsame ∧ UnaryHistory constructorRead ∧ UnaryHistory eliminatorRead ∧
                  List.Mem (kernelInductiveAcceptanceEncodeBHist S)
                    (kernelInductiveAcceptanceToEventFlow packet) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet packetShape unaryD unaryS unaryE constructorRoute eliminatorRoute
  cases packetShape
  have constructorUnary : UnaryHistory constructorRead :=
    unary_cont_closed unaryD unaryS constructorRoute
  have eliminatorUnary : UnaryHistory eliminatorRead :=
    unary_cont_closed constructorUnary unaryE eliminatorRoute
  have sourceAtEliminator : hsame eliminatorRead eliminatorRead ∧ UnaryHistory eliminatorRead :=
    ⟨hsame_refl eliminatorRead, eliminatorUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row eliminatorRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row eliminatorRead ∧ Cont D S constructorRead)
          (fun row : BHist => hsame row eliminatorRead ∧
            Cont constructorRead E eliminatorRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro eliminatorRead sourceAtEliminator
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
      exact ⟨source.left, constructorRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, eliminatorRoute⟩
  }
  have signaturesListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist S)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk D S E P R H C Q N)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist S)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist D, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist S, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist E,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist R,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist Q,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist N]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
  exact ⟨cert, constructorUnary, eliminatorUnary, signaturesListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp

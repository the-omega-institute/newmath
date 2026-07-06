import BEDC.Derived.AuditMapFrontierIndexUp.TasteGate

namespace BEDC.Derived.AuditMapFrontierIndexUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditMapFrontierIndexCarrier_frontier_row_obligation [AskSetup] [PackageSetup]
    {T A E P R O F S H C K N obstructionRead frontierRead consumerRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapFrontierIndexCarrier T A E P R O F S H C K N bundle pkg ->
      Cont R O obstructionRead -> Cont O F frontierRead -> Cont F S consumerRead ->
        Cont K N nameRead -> PkgSig bundle N pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row F ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row A ∨ hsame row E ∨ hsame row P ∨ hsame row R ∨
                hsame row O ∨ hsame row F ∨ hsame row frontierRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont O F frontierRead ∧ Cont F S consumerRead ∧
                PkgSig bundle N pkg)
            hsame ∧ UnaryHistory obstructionRead ∧ UnaryHistory frontierRead ∧
              UnaryHistory consumerRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier obstructionRoute frontierRoute consumerRoute nameRoute namePkg
  obtain ⟨_unaryT, _unaryA, _unaryE, _unaryP, unaryR, unaryO, unaryF, unaryS,
    _unaryH, _unaryC, unaryK, unaryN, _provenancePkg, _carrierNamePkg⟩ := carrier
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed unaryR unaryO obstructionRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed unaryO unaryF frontierRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed unaryF unaryS consumerRoute
  have nameUnary : UnaryHistory nameRead := unary_cont_closed unaryK unaryN nameRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row F ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row A ∨ hsame row E ∨ hsame row P ∨ hsame row R ∨ hsame row O ∨
            hsame row F ∨ hsame row frontierRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont O F frontierRead ∧ Cont F S consumerRead ∧
            PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro F ⟨hsame_refl F, unaryF⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierRoute, consumerRoute, namePkg⟩
  }
  exact ⟨cert, obstructionUnary, frontierUnary, consumerUnary, nameUnary⟩

end BEDC.Derived.AuditMapFrontierIndexUp
